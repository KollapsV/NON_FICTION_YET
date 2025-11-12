/* USER CODE BEGIN Header */
/**
  ******************************************************************************
  * @file           : main.c
  * @brief          : DALI device STM32F103C8T6
  *                   RX: PA3 (TIM2_CH4), TX: PA2 (open-drain)
  *                   PWM: TIM3_CH1, Debug UART: USART1 TX on PA9
  *                   - Addressing (IEC + DLC-02 DATA=0x80 path; broadcast + addressed)
  *                   - Power-on level applied at boot
  *                   - Linear/Log curve switchable
  *                   - Flash persistence:
  *                       * SA in raw cell at 0x08017050 (with page erase @0x08017000)
  *                       * Params blob on last flash page (CRC32)
  *                   - “>70% off” fixed: CCR never 0 or ARR, 5% headroom
  ******************************************************************************
  * Copyright (c) 2025.
  * Licensed AS-IS.
  ******************************************************************************
  */
/* USER CODE END Header */

/* ========================= Includes ====================================== */
#include "main.h"
#include "stm32f1xx_it.h"
#include <math.h>
#include <string.h>
#include <stdio.h>
#include <stdint.h>

/* ========================= DALI Special (Addressing) ===================== */
#define CMD_TERMINATE               0xA1
#define CMD_INITIALISE              0xA5
#define CMD_RANDOMISE               0xA7
#define CMD_COMPARE                 0xA9
#define CMD_WITHDRAW                0xAB
#define CMD_SEARCHADDRH             0xB1
#define CMD_SEARCHADDRM             0xB3
#define CMD_SEARCHADDRL             0xB5
#define CMD_PROGRAM_SHORT_ADDRESS   0xB7
#define CMD_VERIFY_SHORT_ADDRESS    0xB9
#define CMD_QUERY_SHORT_ADDRESS     0xBB
#define CMD_SET_DTR0_SPECIAL        0xA3   /* special: DTR0(data)=xx */

/* DLC-02 alternative configuration path: DATA=0x80 on addressed/broadcast frame */
#define CMD_SET_SHORT_ADDR_DATA     0x80   /* DATA=0x80 → “SET SHORT ADDRESS (DTR0)” */

/* ========================= DALI General (subset) ========================= */
#define CMD_SET_POWER_ON_LEVEL      0x2A
#define CMD_SET_MAX_LEVEL           0x2B
#define CMD_SET_MIN_LEVEL           0x2C
#define CMD_SET_SYSTEM_FAIL_LEVEL   0x2D
#define CMD_ENABLE_DEVICE_TYPE      0xC1
#define CMD_SET_DIMMING_CURVE       0xE3  /* DTR0: 0 = log, 1 = linear */

/* ========================= HW Handles ==================================== */
TIM_HandleTypeDef htim2;
TIM_HandleTypeDef htim3;
TIM_HandleTypeDef htim4;
UART_HandleTypeDef huart1;

/* ========================= Timing / RX Capture =========================== */
#define TIMER_TICK_US       10u
#define MAX_PULSES          64u
#define GAP_US              1000u
#define GAP_TICKS           (GAP_US / TIMER_TICK_US)
#define DALI_HALF_US_HINT   410u   /* ≈416.7 us */

/* ========================= PWM / Curve =================================== */
#define PWM_TIMER           (&htim3)
#define PWM_CHANNEL         TIM_CHANNEL_1
#define PWM_PERIOD_DEFAULT  (4095)
#define PWM_MIN_PCT         0
#define PWM_MAX_PCT         100
#define BRIGHT_GAMMA        2.2f

/* Safety headroom */
#define PWM_HEADROOM_PCT    5u

#define DALI_DAPC_PERMISSIVE        1
#define DALI_ALLOW_BROADCAST_DAPC   1
#define DALI_TX_ONE_HL              0   /* '1' = LH, '0' = HL */

/* ========================= Runtime State ================================= */
static volatile uint8_t  session_active = 0;
static volatile uint8_t  capture_done   = 0;
static volatile uint8_t  expect_rising  = 1;
static volatile uint8_t  have_fall      = 0;
static volatile uint8_t  have_any_edge  = 0;

static volatile uint16_t t_rise = 0;
static volatile uint16_t t_fall_last = 0;
static volatile uint16_t last_edge_cap = 0;

static volatile uint16_t high_ticks[MAX_PULSES];
static volatile uint16_t low_ticks [MAX_PULSES];
static volatile uint8_t  high_cnt = 0;
static volatile uint8_t  low_cnt  = 0;

/* TX state (backward) */
static volatile uint8_t  tx_active = 0;
static volatile uint16_t tx_half_ticks = 0;
static volatile uint8_t  tx_hb[22];
static volatile uint8_t  tx_idx = 0;

/* Commissioning */
static volatile uint8_t  commissioning_mode = 0;
static volatile uint8_t  withdrawn = 0;
static volatile uint8_t  selected  = 0;
static volatile uint32_t randomAddress = 0;
static volatile uint32_t searchAddress = 0;
static volatile uint8_t  dali_dtr0 = 0;

/* Levels/Curve */
static volatile uint16_t arc2pwm_lut[255];
static volatile uint16_t pwm_level = 0;
static volatile uint8_t  curve_linear = 0;         /* 0=log (default), 1=linear */
static volatile uint8_t  commanded_arc_level = 0;
static volatile uint8_t  actual_arc_level    = 0;

/* Address and limits (arc 0..254) */
static volatile uint8_t  dali_short_addr = 1;      /* 0..63 */
static volatile uint8_t  dali_power_on_level    = 128;
static volatile uint8_t  dali_min_level         = 0;
static volatile uint8_t  dali_max_level         = 254;
static volatile uint8_t  dali_system_fail_level = 0;

/* ========================= Flash Persistence ============================= */
#define FLASH_SIZE_REG_ADDR   ((uint32_t)0x1FFFF7E0u) /* 16-bit KB */
#define FLASH_BASE_ADDR       ((uint32_t)0x08000000u)

/* Blob (last page) */
#define PARAM_MAGIC           (0x44504D31u)   /* "DPM1" */
#define PARAM_VERSION         (0x00010008u)   /* bump */
static uint32_t g_param_page_addr = 0x0800FC00u; /* fallback */

/* Raw cell for SA — fixed address + page (allow re-writes via single-page erase) */
#define SA_PAGE_ADDR          ((uint32_t)0x08017000u)
#define SA_CELL_ADDR          ((uint32_t)0x08017050u) /* halfword */

/* ========================= Types ========================================= */
typedef struct {
    uint32_t magic;
    uint32_t version;
    uint32_t crc;
    uint8_t  short_addr;         /* 0..63 or 0xFF=unset */
    uint8_t  curve_linear;       /* 0/1 */
    uint8_t  power_on_level;     /* 0..254 */
    uint8_t  min_level;          /* 0..254 */
    uint8_t  max_level;          /* 0..254 */
    uint8_t  system_fail_level;  /* 0..254 */
    uint8_t  rsv[56];
} __attribute__((packed)) param_blob_t;

/* ========================= Prototypes ==================================== */
void SystemClock_Config(void);
static void MX_GPIO_Init(void);
static void MX_TIM3_Init(void);
static void MX_TIM2_Init(void);
static void MX_TIM4_Init(void);
static void MX_USART1_UART_Init(void);
static void MX_TIM2_Init_10us(void);
static void MX_TIM4_Init_10us(void);

static inline uint16_t dt16(uint16_t a, uint16_t b) { return (uint16_t)(b - a); }
void uart_print(const char *s);

/* CRC / NVM */
static uint32_t crc32_accum(const uint8_t *p, uint32_t len);
static void params_defaults(void);
static void nvm_detect_param_page(void);
static uint8_t params_load_from_flash(void);
static void params_save_to_flash(void);

/* SA raw cell */
static uint8_t sa_cell_load(uint8_t *sa_out);
static void sa_cell_save(uint8_t sa);

/* DALI */
typedef struct {
    uint8_t ok;
    uint8_t is_forward;
    uint8_t bits[40];
    uint8_t bit_count;
    uint8_t addr_or_adr;
    uint8_t data;
} DaliFrame;

static uint32_t prng32(void);
static void commissioning_handle(uint8_t adr_byte, uint8_t data_byte);

static DaliFrame decode_dali(const uint16_t *high, uint8_t hc,
                             const uint16_t *low,  uint8_t lc);
static void print_dali_frame(DaliFrame f);
static uint8_t dali_is_query_opcode(uint8_t op);
static uint8_t dali_build_query_reply(uint8_t opcode, uint8_t *out_byte);
static void dali_send_response(uint8_t data, uint16_t half_ticks);
static void dali_build_tx_halfbits(uint8_t data);
static void print_and_restart(void);

static inline uint16_t clamp16(uint16_t x, uint16_t lo, uint16_t hi) {
    return (x < lo) ? lo : (x > hi ? hi : x);
}
static inline uint16_t pct_to_ccr(uint16_t arr, uint8_t pct) {
    if (pct >= 100) pct = 99;
    uint32_t v = ((uint32_t)(arr+1) * pct) / 100u;
    if (v > arr) v = arr;
    return (uint16_t)v;
}

/* Curve/LUT */
static void rebuild_lut(void);
static void set_arc(uint8_t arc);
static inline uint16_t arc_to_pwm(uint8_t arc) { return arc2pwm_lut[arc]; }
static uint8_t pwm_to_arc(uint16_t lvl) {
    uint16_t best = 0; uint8_t best_idx = 0;
    for (uint8_t i = 1; i <= 254; i++) {
        uint16_t d = (arc2pwm_lut[i] > lvl) ? (arc2pwm_lut[i] - lvl) : (lvl - arc2pwm_lut[i]);
        if (i == 1 || d < best) { best = d; best_idx = i; }
    }
    return best_idx;
}
static void pwm_apply_level(uint16_t lvl) {
    uint16_t arr = __HAL_TIM_GET_AUTORELOAD(PWM_TIMER);
    uint16_t guard = (uint16_t)(((uint32_t)(arr+1) * PWM_HEADROOM_PCT) / 100u);
    if (guard < 1) guard = 1;
    if (lvl >= arr) lvl = arr - guard;
    if (lvl == 0 && pwm_level > 0) lvl = 1;
    pwm_level = clamp16(lvl, 0, arr-1);
    __HAL_TIM_SET_COMPARE(PWM_TIMER, PWM_CHANNEL, pwm_level);
}
static void pwm_set_frequency(uint32_t target_hz) {
    if (target_hz < 200)    target_hz = 200;
    if (target_hz > 20000)  target_hz = 20000;
    uint32_t psc = 71; /* 72 MHz / (71+1) = 1 MHz */
    uint32_t arr = (1000000u / target_hz);
    if (arr == 0) arr = 1;
    arr -= 1;
    if (arr > 0xFFFF) arr = 0xFFFF;

    HAL_TIM_PWM_Stop(&htim3, TIM_CHANNEL_1);
    __HAL_TIM_SET_PRESCALER(&htim3, (uint16_t)psc);
    __HAL_TIM_SET_AUTORELOAD(&htim3, (uint16_t)arr);
    __HAL_TIM_SET_COUNTER(&htim3, 0);

    rebuild_lut();

    pwm_apply_level(pwm_level);
    __HAL_TIM_CLEAR_FLAG(&htim3, TIM_FLAG_UPDATE);
    HAL_TIM_GenerateEvent(&htim3, TIM_EVENTSOURCE_UPDATE);
    HAL_TIM_PWM_Start(&htim3, TIM_CHANNEL_1);
}

/* ========================= CRC32 ========================================= */
static uint32_t crc32_accum(const uint8_t *p, uint32_t len)
{
    uint32_t crc = 0xFFFFFFFFu;
    for (uint32_t i=0;i<len;i++) {
        crc ^= p[i];
        for (uint8_t b=0;b<8;b++) crc = (crc>>1) ^ (0xEDB88320u & (-(int)(crc & 1)));
    }
    return ~crc;
}

/* ========================= NVM Helpers =================================== */
static void params_defaults(void)
{
    dali_short_addr        = 1;
    curve_linear           = 0;
    dali_power_on_level    = 128;
    dali_min_level         = 0;
    dali_max_level         = 254;
    dali_system_fail_level = 0;
}

static void nvm_detect_param_page(void)
{
    uint16_t size_kb = *((uint16_t*)FLASH_SIZE_REG_ADDR);
    if (size_kb == 0 || size_kb > 512) size_kb = 64;
    uint32_t last_page = FLASH_BASE_ADDR + ((uint32_t)size_kb * 1024u) - 1024u;
    if (last_page < FLASH_BASE_ADDR || last_page > (FLASH_BASE_ADDR + 0x20000u - 1024u)) {
        last_page = 0x0800FC00u;
    }
    g_param_page_addr = last_page;
}

static uint8_t params_load_from_flash(void)
{
    const param_blob_t *pb = (const param_blob_t*)g_param_page_addr;
    if (pb->magic != PARAM_MAGIC || pb->version != PARAM_VERSION) return 0;
    uint32_t crc_calc = crc32_accum(((const uint8_t*)pb)+8, sizeof(param_blob_t)-8);
    if (crc_calc != pb->crc) return 0;

    dali_short_addr        = (pb->short_addr <= 63) ? pb->short_addr : 0xFF;
    curve_linear           = pb->curve_linear ? 1 : 0;
    dali_power_on_level    = (pb->power_on_level<=254)?pb->power_on_level:254;
    dali_min_level         = (pb->min_level<=254)?pb->min_level:0;
    dali_max_level         = (pb->max_level<=254)?pb->max_level:254;
    dali_system_fail_level = (pb->system_fail_level<=254)?pb->system_fail_level:0;
    if (dali_min_level > dali_max_level) { dali_min_level = 0; dali_max_level = 254; }
    return 1;
}

static void params_save_to_flash(void)
{
    uart_print("NVM SAVE\r\n");

    __disable_irq();

    param_blob_t out;
    memset(&out,0,sizeof(out));
    out.magic            = PARAM_MAGIC;
    out.version          = PARAM_VERSION;
    out.short_addr       = (uint8_t)((dali_short_addr<=63)?dali_short_addr:0xFF);
    out.curve_linear     = curve_linear ? 1 : 0;
    out.power_on_level   = (dali_power_on_level<=254)?dali_power_on_level:254;
    out.min_level        = (dali_min_level<=254)?dali_min_level:0;
    out.max_level        = (dali_max_level<=254)?dali_max_level:254;
    out.system_fail_level= (dali_system_fail_level<=254)?dali_system_fail_level:0;
    out.crc = crc32_accum(((const uint8_t*)&out)+8, sizeof(out)-8);

    HAL_FLASH_Unlock();

    FLASH_EraseInitTypeDef erase = {0};
    uint32_t page_error = 0xFFFFFFFFu;
    erase.TypeErase   = FLASH_TYPEERASE_PAGES;
    erase.PageAddress = g_param_page_addr;
    erase.NbPages     = 1;
    HAL_FLASHEx_Erase(&erase, &page_error);

    const uint16_t *src = (const uint16_t*)&out;
    uint32_t addr = g_param_page_addr;
    for (uint32_t i=0; i<sizeof(out); i+=2, addr+=2) {
        HAL_FLASH_Program(FLASH_TYPEPROGRAM_HALFWORD, addr, src[i/2]);
    }

    HAL_FLASH_Lock();
    __enable_irq();
}

/* SA raw cell (re-writable: erase 1 page, write halfword) */
static uint8_t sa_cell_load(uint8_t *sa_out)
{
    uint16_t hw = *((volatile uint16_t*)SA_CELL_ADDR);
    if (hw == 0xFFFFu) return 0;
    uint8_t sa = (uint8_t)(hw & 0x3Fu);
    *sa_out = sa;
    char line[64];
    snprintf(line, sizeof(line), "SA CELL LOAD: SA=%u\r\n", (unsigned)sa);
    uart_print(line);
    return 1;
}
static void sa_cell_save(uint8_t sa)
{
    HAL_FLASH_Unlock();
    FLASH_EraseInitTypeDef erase = {0};
    uint32_t page_error = 0xFFFFFFFFu;
    erase.TypeErase   = FLASH_TYPEERASE_PAGES;
    erase.PageAddress = SA_PAGE_ADDR; /* erase single page that holds cell */
    erase.NbPages     = 1;
    HAL_FLASHEx_Erase(&erase, &page_error);

    HAL_FLASH_Program(FLASH_TYPEPROGRAM_HALFWORD, SA_CELL_ADDR, (uint16_t)(sa & 0x3Fu));
    HAL_FLASH_Lock();

    char line[64];
    snprintf(line, sizeof(line), "NVM SAVE SA=%u\r\n", (unsigned)(sa & 0x3F));
    uart_print(line);
}

/* ========================= DALI Core ===================================== */
static uint8_t dali_is_dapc(uint8_t addr, uint8_t data) {
    if (data > 254) return 0;
#if DALI_DAPC_PERMISSIVE
    (void)addr; return 1;
#else
    return ((addr & 0x80) == 0);
#endif
}
static uint8_t dali_addr_matches(uint8_t adr_byte) {
    uint8_t S   = (uint8_t)(adr_byte & 0x01);
    uint8_t A   = (uint8_t)((adr_byte >> 1) & 0x3F);
    uint8_t ours= (uint8_t)(dali_short_addr & 0x3F);
    if (S == 0 && A == ours) return 1;
    else if (adr_byte == ours) return 1;
    else if ((adr_byte & 0x7F) == (uint8_t)(ours << 1)) return 1;
    else return 0;
}

static void dali_apply_arc_level(uint8_t arc)
{
    commanded_arc_level = arc;
    if (arc == 0) {
        pwm_apply_level(0);
        actual_arc_level = 0;
        return;
    }
    uint8_t effective = arc;
    if (effective < dali_min_level) effective = dali_min_level;
    if (effective > dali_max_level) effective = dali_max_level;
    set_arc(effective);
}
static uint8_t dali_apply_action(uint8_t data) {
    switch (data) {
        case 0x00:
            dali_apply_arc_level(0);
            return 1;
        case 0x01:
        case 0x03: {
            uint8_t cur = actual_arc_level;
            if (cur < 254) cur++;
            dali_apply_arc_level(cur);
            return 1;
        }
        case 0x02:
        case 0x04: {
            uint8_t cur = actual_arc_level;
            if (cur > 0) cur--;
            dali_apply_arc_level(cur);
            return 1;
        }
        case 0x05:
            dali_apply_arc_level(dali_max_level);
            return 1;
        case 0x06:
            dali_apply_arc_level(dali_min_level);
            return 1;
        case 0x07: {
            uint8_t cur = actual_arc_level;
            if (cur > 0) cur--;
            dali_apply_arc_level(cur);
            return 1;
        }
        case 0x08: {
            if (actual_arc_level == 0) {
                dali_apply_arc_level(dali_power_on_level);
            } else {
                uint8_t cur = actual_arc_level;
                if (cur < 254) cur++;
                dali_apply_arc_level(cur);
            }
            return 1;
        }
        case 0x10:
            dali_apply_arc_level(dali_max_level);
            return 1;
        default:
            return 0;
    }
}

/* ========================= Commissioning ================================= */
static uint32_t prng32(void) { static uint32_t s=0xA5A55A5Au; s = s*1664525u + 1013904223u; return s; }

static void commissioning_handle(uint8_t adr_byte, uint8_t data_byte)
{
    uint16_t half_ticks = (uint16_t)((DALI_HALF_US_HINT + (TIMER_TICK_US/2)) / TIMER_TICK_US);

    switch (adr_byte) {
        case CMD_INITIALISE:  commissioning_mode = 1; withdrawn = 0; selected = 0; return;
        case CMD_TERMINATE:   commissioning_mode = 0; withdrawn = 0; selected = 0; params_save_to_flash(); return;
        case CMD_RANDOMISE:   if (!commissioning_mode) return; randomAddress = prng32() & 0xFFFFFFu; withdrawn = 0; selected = 0; return;
        case CMD_SET_DTR0_SPECIAL: dali_dtr0 = data_byte; return;
        case CMD_SEARCHADDRH: if (!commissioning_mode) return; searchAddress = (searchAddress & 0x00FFFFu) | ((uint32_t)data_byte << 16); return;
        case CMD_SEARCHADDRM: if (!commissioning_mode) return; searchAddress = (searchAddress & 0xFF00FFu) | ((uint32_t)data_byte << 8);  return;
        case CMD_SEARCHADDRL: if (!commissioning_mode) return; searchAddress = (searchAddress & 0xFFFF00u) | (uint32_t)data_byte;        return;
        case CMD_COMPARE:
            if (!commissioning_mode) return;
            selected = (randomAddress == searchAddress) ? 1u : 0u;
            if (!withdrawn && (randomAddress <= searchAddress)) dali_send_response(0xFF, half_ticks);
            return;
        case CMD_WITHDRAW:
            if (!commissioning_mode) return;
            if (selected && !withdrawn) withdrawn = 1;
            selected = 0; return;
        case CMD_PROGRAM_SHORT_ADDRESS:
            if (!commissioning_mode) return;
            if (selected && !withdrawn) {
                dali_short_addr = (uint8_t)(dali_dtr0 & 0x3F);
                withdrawn = 1; selected = 0;
                sa_cell_save(dali_short_addr);
                params_save_to_flash();
            }
            return;
        case CMD_VERIFY_SHORT_ADDRESS:
            if (!commissioning_mode) return;
            if ((uint8_t)(dali_dtr0 & 0x3F) == (uint8_t)(dali_short_addr & 0x3F)) dali_send_response(0xFF, half_ticks);
            return;
        case CMD_QUERY_SHORT_ADDRESS:
            if (!commissioning_mode) return;
            dali_send_response((uint8_t)(dali_short_addr & 0x3F), half_ticks);
            return;
        default: return;
    }
}

/* ========================= RX/TX/Decode ================================== */
void uart_print(const char *s) { HAL_UART_Transmit(&huart1, (uint8_t*)s, (uint16_t)strlen(s), HAL_MAX_DELAY); }

static inline void ArmGapWatchdog(void)
{
    if (!session_active) return;
    uint16_t now = __HAL_TIM_GET_COUNTER(&htim2);
    __HAL_TIM_SET_COMPARE(&htim2, TIM_CHANNEL_3, (uint16_t)(now + GAP_TICKS));
    __HAL_TIM_CLEAR_FLAG(&htim2, TIM_FLAG_CC3);
    __HAL_TIM_ENABLE_IT(&htim2, TIM_IT_CC3);
}

static void dali_build_tx_halfbits(uint8_t data)
{
    uint8_t i = 0;
#if DALI_TX_ONE_HL
    tx_hb[i++] = 1; tx_hb[i++] = 0;        /* start '1' = HL */
#else
    tx_hb[i++] = 0; tx_hb[i++] = 1;        /* start '1' = LH */
#endif
    for (int b = 7; b >= 0; b--) {
        uint8_t v = (data >> b) & 1;
#if DALI_TX_ONE_HL
        if (v) { tx_hb[i++] = 1; tx_hb[i++] = 0; }
        else   { tx_hb[i++] = 0; tx_hb[i++] = 1; }
#else
        if (v) { tx_hb[i++] = 0; tx_hb[i++] = 1; }
        else   { tx_hb[i++] = 1; tx_hb[i++] = 0; }
#endif
    }
    tx_hb[i++] = 1; tx_hb[i++] = 1; tx_hb[i++] = 1; tx_hb[i++] = 1;  /* 2 stop bits */
}

static void dali_send_response(uint8_t data, uint16_t half_ticks)
{
    if (tx_active) return;
    dali_build_tx_halfbits(data);
    tx_half_ticks = half_ticks;
    tx_active = 1;
    tx_idx = 0;
    HAL_GPIO_WritePin(GPIOA, GPIO_PIN_2, GPIO_PIN_SET);   /* idle high */
    __HAL_TIM_SET_COUNTER(&htim4, 0);
    __HAL_TIM_CLEAR_FLAG(&htim4, TIM_FLAG_UPDATE);
    /* Start ≈ 12Te after last edge (window 7..22Te) */
    __HAL_TIM_SET_AUTORELOAD(&htim4, (uint16_t)(12u * half_ticks));
    HAL_TIM_Base_Start_IT(&htim4);
}

static uint8_t build_bits_from_halfbits(const uint8_t *hb, uint16_t hb_cnt,
                                        uint8_t phase, uint8_t polarityA,
                                        uint8_t *out_bits, uint8_t out_max) {
    uint16_t k = phase; uint8_t nb = 0;
    while (k + 1 < hb_cnt && nb < out_max) {
        uint8_t a = hb[k], b = hb[k+1], bit;
        if (polarityA) { if (a==1 && b==0) bit=1; else if (a==0 && b==1) bit=0; else bit=2; }
        else           { if (a==0 && b==1) bit=1; else if (a==1 && b==0) bit=0; else bit=2; }
        out_bits[nb++] = bit; k += 2;
    }
    return nb;
}
static DaliFrame check_candidate(uint8_t *bits, uint8_t nb) {
    DaliFrame f = (DaliFrame){0};
    if (nb < 11) return f;
    /* backward short (11 bits) */
    for (uint8_t s = 0; s + 11 <= nb; s++) {
        if (bits[s]==1 && bits[s+9]==1 && bits[s+10]==1) {
            f.ok=1; f.is_forward=0; f.bit_count=11;
            for (uint8_t i=0;i<11;i++) f.bits[i]=bits[s+i];
            uint8_t val=0; for (uint8_t i=1;i<=8;i++) val=(val<<1)|(f.bits[i]&1);
            f.data=val; return f;
        }
    }
    /* forward 17..19 bits */
    for (uint8_t need = 19; need >= 17; need--) {
        for (uint8_t s = 0; s + need <= nb; s++) {
            if (bits[s] != 1) continue;
            if (need >= 18 && bits[s+17] == 0) continue;
            if (need >= 19 && bits[s+18] == 0) continue;
            f.ok=1; f.is_forward=1; f.bit_count=need;
            for (uint8_t i=0;i<need;i++) f.bits[i]=bits[s+i];
            uint8_t adr=0, dat=0;
            for (uint8_t i=1;i<=8;i++)  adr=(adr<<1)|(f.bits[i]&1);
            for (uint8_t i=9;i<=16;i++) dat=(dat<<1)|(f.bits[i]&1);
            f.addr_or_adr=adr; f.data=dat; return f;
        }
        if (need==17) break;
    }
    return f;
}
static DaliFrame decode_dali(const uint16_t *high, uint8_t hc,
                             const uint16_t *low,  uint8_t lc) {
    DaliFrame out = (DaliFrame){0};
    if (hc==0 && lc==0) return out;
    uint16_t half_ticks = (uint16_t)((DALI_HALF_US_HINT + (TIMER_TICK_US/2)) / TIMER_TICK_US);
    if (half_ticks == 0) half_ticks = 1;
    uint8_t  hb_level[2*MAX_PULSES*2];
    uint16_t hb_cnt = 0;
    for (uint8_t i = 0; i < hc || i < lc; i++) {
        if (i < hc) {
            uint16_t d = high[i];
            uint16_t n = (d + (half_ticks/2)) / half_ticks;
            if (n < 1) n = 1; if (n > 2) n = 2;
            while (n-- && hb_cnt < sizeof(hb_level)) hb_level[hb_cnt++] = 1;
        }
        if (i < lc) {
            uint16_t d = low[i];
            uint16_t n = (d + (half_ticks/2)) / half_ticks;
            if (n < 1) n = 1; if (n > 2) n = 2;
            while (n-- && hb_cnt < sizeof(hb_level)) hb_level[hb_cnt++] = 0;
        }
    }
    uint8_t bits[40];
    uint8_t nb = build_bits_from_halfbits(hb_level, hb_cnt, 0, 1, bits, sizeof(bits));
    DaliFrame f = check_candidate(bits, nb);
    if (f.ok && f.is_forward && f.bit_count < 19) while (f.bit_count < 19) f.bits[f.bit_count++] = 1;
    return f;
}

static uint8_t dali_is_query_opcode(uint8_t op) {
    switch (op) {
        case 0x90: case 0x91: case 0x92: case 0x93: case 0x94:
        case 0x95: case 0x96: case 0x97: case 0x98: case 0x99:
        case 0x9A: case 0x9B: case 0xA0: case 0xA1: case 0xA2:
        case 0xA3: case 0xA4: case 0xA5:
            return 1;
        default: return 0;
    }
}

static uint8_t dali_build_query_reply(uint8_t opcode, uint8_t *out_byte) {
    uint8_t reply;
    switch (opcode) {
        case 0x91: /* QUERY CONTROL GEAR PRESENT */
            reply = 0xFF;
            break;

        case 0x97: reply = 0x01; break;            /* VERSION NUMBER */
        case 0x99: reply = 0x06; break;            /* DEVICE TYPE = 6 */

        case 0xA0: reply = actual_arc_level; break; /* ACTUAL LEVEL */
        case 0xA1: reply = dali_max_level; break;
        case 0xA2: reply = dali_min_level; break;
        case 0xA3: reply = dali_power_on_level; break;
        case 0xA4: reply = dali_system_fail_level; break;
        case 0x9B: reply = dali_dtr0; break;

        case 0x90: default: {
            /* QUERY STATUS */
            uint8_t lamp_failure = 0;
            uint8_t arc_on   = (actual_arc_level > 0) ? 1 : 0;
            uint8_t limit_err= 0;
            uint8_t clamped = commanded_arc_level;
            if (clamped > 0) {
                if (clamped < dali_min_level) clamped = dali_min_level;
                if (clamped > dali_max_level) clamped = dali_max_level;
            } else {
                clamped = 0;
            }
            if (actual_arc_level != clamped) {
                limit_err = 1;
            }
            reply = (lamp_failure?0x80:0) | (arc_on?0x40:0) | (limit_err?0x20:0);
            break;
        }
    }
    *out_byte = reply; return 1;
}

static void print_dali_frame(DaliFrame f) {
    char line[64];
    if (!f.ok) { uart_print("DALI: frame not recognized\r\n"); return; }
    if (f.is_forward) {
        snprintf(line, sizeof(line), "DALI forward: ADDR=0x%02X, DATA=0x%02X\r\n", (unsigned)f.addr_or_adr, (unsigned)f.data);
        uart_print(line);
    } else {
        snprintf(line, sizeof(line), "DALI backward: DATA=0x%02X\r\n", (unsigned)f.data);
        uart_print(line);
    }
}

/* ========================= Curve/LUT ===================================== */
static void rebuild_lut(void)
{
    uint16_t arr = __HAL_TIM_GET_AUTORELOAD(PWM_TIMER);
    uint16_t guard = (uint16_t)(((uint32_t)(arr+1) * PWM_HEADROOM_PCT) / 100u);
    if (guard < 1) guard = 1;
    uint16_t pwm_min = pct_to_ccr(arr, PWM_MIN_PCT);
    uint16_t pwm_max = (arr > guard) ? (arr - guard) : (arr - 1);
    if (pwm_max <= pwm_min) pwm_max = pwm_min + 1;

    for (int a = 0; a <= 254; a++) {
        uint8_t aa = (uint8_t)a;
        if (aa < dali_min_level) aa = dali_min_level;
        if (aa > dali_max_level) aa = dali_max_level;

        uint32_t v;
        if (curve_linear) {
            uint32_t den = (dali_max_level > dali_min_level) ? (uint32_t)(dali_max_level - dali_min_level) : 1u;
            uint32_t num = (uint32_t)(aa - dali_min_level);
            uint32_t frac = (num * 10000u) / den;
            v = pwm_min + ((uint32_t)(pwm_max - pwm_min) * frac) / 10000u;
        } else {
            float x0 = (float)(aa - dali_min_level) / (float)((dali_max_level > dali_min_level) ? (dali_max_level - dali_min_level) : 1);
            if (x0 < 0.0f) x0 = 0.0f; if (x0 > 1.0f) x0 = 1.0f;
            float y  = powf(x0, BRIGHT_GAMMA);
            float vf = (float)pwm_min + (float)(pwm_max - pwm_min) * y;
            if (vf < 1.f && aa>0) vf = 1.f;
            v = (uint32_t)(vf + 0.5f);
        }
        if (v > (uint32_t)pwm_max) v = pwm_max;
        arc2pwm_lut[a] = (a==0) ? 0 : (uint16_t)v;
    }
}
static void set_arc(uint8_t arc)
{
    if (arc > 254) arc = 254;
    uint16_t arr = __HAL_TIM_GET_AUTORELOAD(PWM_TIMER);
    uint16_t guard = (uint16_t)(((uint32_t)(arr+1) * PWM_HEADROOM_PCT) / 100u);
    if (guard < 1) guard = 1;

    uint16_t c = arc2pwm_lut[arc];
    if (arc > 0 && c == 0) c = 1;
    if (c >= arr) c = arr - guard;
    pwm_apply_level(c);
    actual_arc_level = arc;
}

/* ========================= Print + Actions =============================== */
static void print_and_restart(void)
{
    DaliFrame fr = decode_dali((const uint16_t*)high_ticks, high_cnt,
                               (const uint16_t*)low_ticks,  low_cnt);

    if (fr.ok && fr.is_forward) {
        switch (fr.addr_or_adr) {
            case CMD_INITIALISE: case CMD_TERMINATE: case CMD_RANDOMISE:
            case CMD_SEARCHADDRH: case CMD_SEARCHADDRM: case CMD_SEARCHADDRL:
            case CMD_COMPARE: case CMD_WITHDRAW:
            case CMD_PROGRAM_SHORT_ADDRESS: case CMD_VERIFY_SHORT_ADDRESS:
            case CMD_QUERY_SHORT_ADDRESS: case CMD_SET_DTR0_SPECIAL:
                commissioning_handle(fr.addr_or_adr, fr.data);
                goto after_actions;
            default: break;
        }

        /* DLC-02 addressed/broadcast path: DATA==0x80 → write SA from DTR0 */
        if (commissioning_mode && fr.data == CMD_SET_SHORT_ADDR_DATA) {
            uint8_t is_broadcast = (fr.addr_or_adr == 0xFF);
            uint8_t addr_ok      = dali_addr_matches(fr.addr_or_adr);
            if (is_broadcast || addr_ok) {
                dali_short_addr = (uint8_t)(dali_dtr0 & 0x3F);
                withdrawn = 1; selected  = 0;
                sa_cell_save(dali_short_addr);
                params_save_to_flash();
                print_dali_frame(fr);
                uart_print("--- done ---\r\n");
                goto restart_capture;
            }
        }

        /* Config writes (addr or broadcast) */
        {
            uint8_t is_broadcast = (fr.addr_or_adr == 0xFF);
            uint8_t addr_ok = dali_addr_matches(fr.addr_or_adr);
            if (addr_ok || is_broadcast) {
                switch (fr.data) {
                    case CMD_ENABLE_DEVICE_TYPE: break;
                    case CMD_SET_POWER_ON_LEVEL:
                        dali_power_on_level = (dali_dtr0<=254)?dali_dtr0:254;
                        params_save_to_flash(); break;
                    case CMD_SET_MAX_LEVEL:
                        dali_max_level = (dali_dtr0<=254)?dali_dtr0:254;
                        if (dali_min_level > dali_max_level) dali_min_level = 0;
                        rebuild_lut(); params_save_to_flash(); break;
                    case CMD_SET_MIN_LEVEL:
                        dali_min_level = (dali_dtr0<=254)?dali_dtr0:0;
                        if (dali_min_level > dali_max_level) dali_max_level = 254;
                        rebuild_lut(); params_save_to_flash(); break;
                    case CMD_SET_SYSTEM_FAIL_LEVEL:
                        dali_system_fail_level = (dali_dtr0<=254)?dali_dtr0:0;
                        params_save_to_flash(); break;
                    case CMD_SET_DIMMING_CURVE:
                        curve_linear = (dali_dtr0 & 0x01) ? 1 : 0;
                        rebuild_lut(); params_save_to_flash(); break;
                    default: break;
                }
            }
        }
    }

    if (fr.ok) {
        const uint8_t is_broadcast = (fr.addr_or_adr == 0xFF);
        const uint8_t addr_ok      = dali_addr_matches(fr.addr_or_adr);

        if (dali_is_dapc(fr.addr_or_adr, fr.data)) {
            dali_apply_arc_level(fr.data);
        }
        if (fr.is_forward && (addr_ok || is_broadcast)) {
            (void)dali_apply_action(fr.data);
        }
        if (fr.is_forward && !is_broadcast && addr_ok && dali_is_query_opcode(fr.data)) {
            uint8_t resp;
            if (dali_build_query_reply(fr.data, &resp)) {
                uint16_t half_ticks = (uint16_t)((DALI_HALF_US_HINT + (TIMER_TICK_US/2)) / TIMER_TICK_US);
                dali_send_response(resp, half_ticks);
            }
        }
    }

after_actions:
    print_dali_frame(fr);
    uart_print("--- done ---\r\n");

restart_capture:
    high_cnt=0; low_cnt=0;
    expect_rising=1; have_any_edge=0; have_fall=0;
    capture_done=0; session_active=0;
    __HAL_TIM_SET_COUNTER(&htim2, 0);
    HAL_TIM_IC_Start_IT(&htim2, TIM_CHANNEL_4);
    HAL_TIM_OC_Start_IT(&htim2, TIM_CHANNEL_3);
}

/* ========================= HAL Callbacks ================================= */
void HAL_TIM_IC_CaptureCallback(TIM_HandleTypeDef *htim)
{
    if (htim->Instance != TIM2 || htim->Channel != HAL_TIM_ACTIVE_CHANNEL_4) return;
    uint16_t cap = HAL_TIM_ReadCapturedValue(htim, TIM_CHANNEL_4);
    if (!session_active) session_active = 1;
    ArmGapWatchdog();

    if (have_any_edge) {
        uint16_t delta_edges = dt16(last_edge_cap, cap);
        if (delta_edges > GAP_TICKS && (high_cnt > 0 || low_cnt > 0)) {
            __HAL_TIM_DISABLE_IT(&htim2, TIM_IT_CC3);
            HAL_TIM_IC_Stop_IT(&htim2, TIM_CHANNEL_4);
            capture_done = 1;
            return;
        }
    }
    last_edge_cap = cap;
    have_any_edge = 1;

    if (expect_rising) {
        if (have_fall && low_cnt < MAX_PULSES) {
            low_ticks[low_cnt++] = dt16(t_fall_last, cap);
            if (low_cnt >= MAX_PULSES) {
                __HAL_TIM_DISABLE_IT(&htim2, TIM_IT_CC3);
                HAL_TIM_IC_Stop_IT(&htim2, TIM_CHANNEL_4);
                capture_done = 1; return;
            }
        }
        t_rise = cap; expect_rising = 0;
        TIM_IC_InitTypeDef s = {0};
        s.ICPolarity  = TIM_INPUTCHANNELPOLARITY_FALLING;
        s.ICSelection = TIM_ICSELECTION_DIRECTTI;
        s.ICPrescaler = TIM_ICPSC_DIV1;
        s.ICFilter    = 0;
        HAL_TIM_IC_ConfigChannel(&htim2, &s, TIM_CHANNEL_4);
        HAL_TIM_IC_Start_IT(&htim2, TIM_CHANNEL_4);
    } else {
        if (high_cnt < MAX_PULSES) {
            high_ticks[high_cnt++] = dt16(t_rise, cap);
            if (high_cnt >= MAX_PULSES) {
                __HAL_TIM_DISABLE_IT(&htim2, TIM_IT_CC3);
                HAL_TIM_IC_Stop_IT(&htim2, TIM_CHANNEL_4);
                capture_done = 1; return;
            }
        }
        t_fall_last = cap; have_fall = 1; expect_rising = 1;
        TIM_IC_InitTypeDef s = {0};
        s.ICPolarity  = TIM_INPUTCHANNELPOLARITY_RISING;
        s.ICSelection = TIM_ICSELECTION_DIRECTTI;
        s.ICPrescaler = TIM_ICPSC_DIV1;
        s.ICFilter    = 0;
        HAL_TIM_IC_ConfigChannel(&htim2, &s, TIM_CHANNEL_4);
        HAL_TIM_IC_Start_IT(&htim2, TIM_CHANNEL_4);
    }
}
void HAL_TIM_OC_DelayElapsedCallback(TIM_HandleTypeDef *htim)
{
    if (htim->Instance == TIM2 && htim->Channel == HAL_TIM_ACTIVE_CHANNEL_3) {
        __HAL_TIM_DISABLE_IT(&htim2, TIM_IT_CC3);
        uint16_t cap = __HAL_TIM_GET_COUNTER(&htim2);
        if (session_active && (high_cnt > 0 || low_cnt > 0)) {
            if (expect_rising) {
                if (have_fall && low_cnt < MAX_PULSES) low_ticks[low_cnt++] = dt16(t_fall_last, cap);
            } else {
                if (high_cnt < MAX_PULSES) high_ticks[high_cnt++] = dt16(t_rise, cap);
            }
            HAL_TIM_IC_Stop_IT(&htim2, TIM_CHANNEL_4);
            capture_done = 1;
        } else {
            session_active = 0;
        }
    }
}
/* TIM4 drives backward bitstream */
void TIM4_IRQHandler(void)
{
    if (__HAL_TIM_GET_FLAG(&htim4, TIM_FLAG_UPDATE) != RESET) {
        if (__HAL_TIM_GET_IT_SOURCE(&htim4, TIM_IT_UPDATE) != RESET) {
            __HAL_TIM_CLEAR_IT(&htim4, TIM_IT_UPDATE);
            if (!tx_active) { HAL_TIM_Base_Stop_IT(&htim4); return; }
            uint8_t lvl = tx_hb[tx_idx];
            if (lvl) HAL_GPIO_WritePin(GPIOA, GPIO_PIN_2, GPIO_PIN_SET);
            else     HAL_GPIO_WritePin(GPIOA, GPIO_PIN_2, GPIO_PIN_RESET);
            tx_idx++;
            if (tx_idx >= 22) {
                HAL_GPIO_WritePin(GPIOA, GPIO_PIN_2, GPIO_PIN_SET);
                HAL_TIM_Base_Stop_IT(&htim4);
                tx_active = 0;
            } else {
                __HAL_TIM_SET_AUTORELOAD(&htim4, tx_half_ticks);
            }
        }
    }
}

/* ========================= Main ========================================== */
int main(void)
{
  HAL_Init();
  SystemClock_Config();

  MX_GPIO_Init();
  MX_TIM3_Init();
  MX_TIM2_Init();
  MX_TIM4_Init();
  MX_USART1_UART_Init();

  nvm_detect_param_page();

  HAL_GPIO_WritePin(GPIOB, GPIO_PIN_12, GPIO_PIN_SET);
  HAL_GPIO_WritePin(GPIOA, GPIO_PIN_2, GPIO_PIN_SET);

  HAL_TIM_PWM_Start(&htim3, TIM_CHANNEL_1);
  __HAL_TIM_SET_COMPARE(&htim3, TIM_CHANNEL_1, 10);

  MX_TIM2_Init_10us();
  MX_TIM4_Init_10us();

  /* Load order: blob → defaults → SA cell override → optional blob sync */
  uint8_t loaded = params_load_from_flash();
  if (!loaded) {
      uart_print("NVM default\r\n");
      params_defaults();
  }

  uint8_t sa_tmp;
  if (sa_cell_load(&sa_tmp)) {
      if (sa_tmp <= 63) {
          dali_short_addr = sa_tmp;
          if (!loaded) {
              uart_print("NVM SYNC (blob <- raw cell)\r\n");
              params_save_to_flash();
          }
      }
  }

  {
      char line[96];
      snprintf(line, sizeof(line), "NVM OK: SA=%u log=%u POL=%u MIN=%u MAX=%u\r\n",
               (unsigned)((dali_short_addr<=63)?dali_short_addr:0xFF),
               (unsigned)curve_linear,
               (unsigned)dali_power_on_level,
               (unsigned)dali_min_level,
               (unsigned)dali_max_level);
      uart_print(line);
  }

  rebuild_lut();
  pwm_set_frequency(1000);
  dali_apply_arc_level(dali_power_on_level);

  high_cnt = low_cnt = 0;
  expect_rising  = 1;
  have_any_edge  = 0;
  have_fall      = 0;
  HAL_TIM_IC_Start_IT(&htim2, TIM_CHANNEL_4);
  HAL_TIM_OC_Start_IT(&htim2, TIM_CHANNEL_3);

  for (;;) {
      if (capture_done) { print_and_restart(); }
  }
}

/* ========================= HAL Init ====================================== */
void SystemClock_Config(void)
{
  RCC_OscInitTypeDef RCC_OscInitStruct = {0};
  RCC_ClkInitTypeDef RCC_ClkInitStruct = {0};
  RCC_OscInitStruct.OscillatorType = RCC_OSCILLATORTYPE_HSE;
  RCC_OscInitStruct.HSEState = RCC_HSE_ON;
  RCC_OscInitStruct.HSEPredivValue = RCC_HSE_PREDIV_DIV1;
  RCC_OscInitStruct.HSIState = RCC_HSI_ON;
  RCC_OscInitStruct.PLL.PLLState = RCC_PLL_ON;
  RCC_OscInitStruct.PLL.PLLSource = RCC_PLLSOURCE_HSE;
  RCC_OscInitStruct.PLL.PLLMUL = RCC_PLL_MUL9;
  if (HAL_RCC_OscConfig(&RCC_OscInitStruct) != HAL_OK) { Error_Handler(); }

  RCC_ClkInitStruct.ClockType = RCC_CLOCKTYPE_HCLK|RCC_CLOCKTYPE_SYSCLK
                              |RCC_CLOCKTYPE_PCLK1|RCC_CLOCKTYPE_PCLK2;
  RCC_ClkInitStruct.SYSCLKSource = RCC_SYSCLKSOURCE_PLLCLK;
  RCC_ClkInitStruct.AHBCLKDivider = RCC_SYSCLK_DIV1;
  RCC_ClkInitStruct.APB1CLKDivider = RCC_HCLK_DIV2;
  RCC_ClkInitStruct.APB2CLKDivider = RCC_HCLK_DIV1;
  if (HAL_RCC_ClockConfig(&RCC_ClkInitStruct, FLASH_LATENCY_2) != HAL_OK) { Error_Handler(); }
}

static void MX_TIM2_Init(void)
{
  TIM_ClockConfigTypeDef sClockSourceConfig = {0};
  TIM_MasterConfigTypeDef sMasterConfig = {0};
  TIM_OC_InitTypeDef sConfigOC = {0};
  TIM_IC_InitTypeDef sConfigIC = {0};

  htim2.Instance = TIM2;
  htim2.Init.Prescaler = 719;
  htim2.Init.CounterMode = TIM_COUNTERMODE_UP;
  htim2.Init.Period = 65535;
  htim2.Init.ClockDivision = TIM_CLOCKDIVISION_DIV1;
  htim2.Init.AutoReloadPreload = TIM_AUTORELOAD_PRELOAD_DISABLE;
  if (HAL_TIM_Base_Init(&htim2) != HAL_OK) { Error_Handler(); }
  sClockSourceConfig.ClockSource = TIM_CLOCKSOURCE_INTERNAL;
  if (HAL_TIM_ConfigClockSource(&htim2, &sClockSourceConfig) != HAL_OK) { Error_Handler(); }
  if (HAL_TIM_OC_Init(&htim2) != HAL_OK) { Error_Handler(); }
  if (HAL_TIM_IC_Init(&htim2) != HAL_OK) { Error_Handler(); }
  sMasterConfig.MasterOutputTrigger = TIM_TRGO_RESET;
  sMasterConfig.MasterSlaveMode = TIM_MASTERSLAVEMODE_DISABLE;
  if (HAL_TIMEx_MasterConfigSynchronization(&htim2, &sMasterConfig) != HAL_OK) { Error_Handler(); }
  sConfigOC.OCMode = TIM_OCMODE_TIMING;
  sConfigOC.Pulse = 0;
  sConfigOC.OCPolarity = TIM_OCPOLARITY_HIGH;
  sConfigOC.OCFastMode = TIM_OCFAST_DISABLE;
  if (HAL_TIM_OC_ConfigChannel(&htim2, &sConfigOC, TIM_CHANNEL_3) != HAL_OK) { Error_Handler(); }  /* CH3 watchdog */

  sConfigIC.ICPolarity = TIM_INPUTCHANNELPOLARITY_RISING;
  sConfigIC.ICSelection = TIM_ICSELECTION_DIRECTTI;
  sConfigIC.ICPrescaler = TIM_ICPSC_DIV1;
  sConfigIC.ICFilter = 0;
  if (HAL_TIM_IC_ConfigChannel(&htim2, &sConfigIC, TIM_CHANNEL_4) != HAL_OK) { Error_Handler(); }

  TIM_IC_InitTypeDef sIC = {0};
  sIC.ICPolarity  = TIM_INPUTCHANNELPOLARITY_RISING;
  sIC.ICSelection = TIM_ICSELECTION_DIRECTTI;
  sIC.ICPrescaler = TIM_ICPSC_DIV1;
  sIC.ICFilter    = 0;
  HAL_TIM_IC_ConfigChannel(&htim2, &sIC, TIM_CHANNEL_4);
  HAL_TIM_IC_Start_IT(&htim2, TIM_CHANNEL_4);

  HAL_TIM_MspPostInit(&htim2);
}

static void MX_TIM3_Init(void)
{
  TIM_ClockConfigTypeDef sClockSourceConfig = {0};
  TIM_MasterConfigTypeDef sMasterConfig = {0};
  TIM_OC_InitTypeDef sConfigOC = {0};

  htim3.Instance = TIM3;
  htim3.Init.Prescaler = 71;
  htim3.Init.CounterMode = TIM_COUNTERMODE_UP;
  htim3.Init.Period = PWM_PERIOD_DEFAULT;
  htim3.Init.ClockDivision = TIM_CLOCKDIVISION_DIV1;
  htim3.Init.AutoReloadPreload = TIM_AUTORELOAD_PRELOAD_DISABLE;
  if (HAL_TIM_Base_Init(&htim3) != HAL_OK) { Error_Handler(); }
  sClockSourceConfig.ClockSource = TIM_CLOCKSOURCE_INTERNAL;
  if (HAL_TIM_ConfigClockSource(&htim3, &sClockSourceConfig) != HAL_OK) { Error_Handler(); }
  if (HAL_TIM_PWM_Init(&htim3) != HAL_OK) { Error_Handler(); }
  sMasterConfig.MasterOutputTrigger = TIM_TRGO_RESET;
  sMasterConfig.MasterSlaveMode = TIM_MASTERSLAVEMODE_DISABLE;
  if (HAL_TIMEx_MasterConfigSynchronization(&htim3, &sMasterConfig) != HAL_OK) { Error_Handler(); }
  sConfigOC.OCMode = TIM_OCMODE_PWM1;
  sConfigOC.Pulse = 100;
  sConfigOC.OCPolarity = TIM_OCPOLARITY_HIGH;
  sConfigOC.OCFastMode = TIM_OCFAST_DISABLE;
  if (HAL_TIM_PWM_ConfigChannel(&htim3, &sConfigOC, TIM_CHANNEL_1) != HAL_OK) { Error_Handler(); }
  HAL_TIM_MspPostInit(&htim3);
}

static void MX_TIM4_Init(void)
{
  TIM_ClockConfigTypeDef sClockSourceConfig = {0};
  TIM_MasterConfigTypeDef sMasterConfig = {0};
  htim4.Instance = TIM4;
  htim4.Init.Prescaler = 719;
  htim4.Init.CounterMode = TIM_COUNTERMODE_UP;
  htim4.Init.Period = 65535;
  htim4.Init.ClockDivision = TIM_CLOCKDIVISION_DIV1;
  htim4.Init.AutoReloadPreload = TIM_AUTORELOAD_PRELOAD_DISABLE;
  if (HAL_TIM_Base_Init(&htim4) != HAL_OK) { Error_Handler(); }
  sClockSourceConfig.ClockSource = TIM_CLOCKSOURCE_INTERNAL;
  if (HAL_TIM_ConfigClockSource(&htim4, &sClockSourceConfig) != HAL_OK) { Error_Handler(); }
  sMasterConfig.MasterOutputTrigger = TIM_TRGO_RESET;
  sMasterConfig.MasterSlaveMode = TIM_MASTERSLAVEMODE_DISABLE;
  if (HAL_TIMEx_MasterConfigSynchronization(&htim4, &sMasterConfig) != HAL_OK) { Error_Handler(); }
}

static void MX_USART1_UART_Init(void)
{
  huart1.Instance = USART1;
  huart1.Init.BaudRate = 115200;
  huart1.Init.WordLength = UART_WORDLENGTH_8B;
  huart1.Init.StopBits = UART_STOPBITS_1;
  huart1.Init.Parity = UART_PARITY_NONE;
  huart1.Init.Mode = UART_MODE_TX_RX;
  huart1.Init.HwFlowCtl = UART_HWCONTROL_NONE;
  huart1.Init.OverSampling = UART_OVERSAMPLING_16;
  if (HAL_UART_Init(&huart1) != HAL_OK) { Error_Handler(); }
}

static void MX_GPIO_Init(void)
{
  GPIO_InitTypeDef GPIO_InitStruct = {0};
  __HAL_RCC_GPIOD_CLK_ENABLE();
  __HAL_RCC_GPIOA_CLK_ENABLE();
  __HAL_RCC_GPIOB_CLK_ENABLE();

  /* DALI TX pin PA2: open-drain, idle HIGH */
  GPIO_InitStruct.Pin = GPIO_PIN_2;
  GPIO_InitStruct.Mode = GPIO_MODE_OUTPUT_OD;
  GPIO_InitStruct.Pull = GPIO_NOPULL;
  GPIO_InitStruct.Speed = GPIO_SPEED_FREQ_LOW;
  HAL_GPIO_Init(GPIOA, &GPIO_InitStruct);
  HAL_GPIO_WritePin(GPIOA, GPIO_PIN_2, GPIO_PIN_SET);

  /* PB12: user LED / debug */
  GPIO_InitStruct.Pin = GPIO_PIN_12;
  GPIO_InitStruct.Mode = GPIO_MODE_OUTPUT_PP;
  GPIO_InitStruct.Pull = GPIO_NOPULL;
  GPIO_InitStruct.Speed = GPIO_SPEED_FREQ_LOW;
  HAL_GPIO_Init(GPIOB, &GPIO_InitStruct);
  HAL_GPIO_WritePin(GPIOB, GPIO_PIN_12, GPIO_PIN_SET);

  /* PA3: TIM2_CH4 input (DALI RX) */
  GPIO_InitTypeDef g = {0};
  g.Pin  = GPIO_PIN_3;
  g.Mode = GPIO_MODE_INPUT;
  g.Pull = GPIO_NOPULL;
  HAL_GPIO_Init(GPIOA, &g);
}

static void MX_TIM2_Init_10us(void)
{
    __HAL_RCC_TIM2_CLK_ENABLE();
    htim2.Instance = TIM2;
    htim2.Init.Prescaler         = 719;           /* 10us */
    htim2.Init.CounterMode       = TIM_COUNTERMODE_UP;
    htim2.Init.Period            = 0xFFFF;
    htim2.Init.ClockDivision     = TIM_CLOCKDIVISION_DIV1;
    htim2.Init.AutoReloadPreload = TIM_AUTORELOAD_PRELOAD_DISABLE;
    HAL_TIM_Base_Init(&htim2);

    TIM_IC_InitTypeDef ic = {0};
    ic.ICPolarity  = TIM_INPUTCHANNELPOLARITY_RISING;
    ic.ICSelection = TIM_ICSELECTION_DIRECTTI;
    ic.ICPrescaler = TIM_ICPSC_DIV1;
    ic.ICFilter    = 0;
    HAL_TIM_IC_ConfigChannel(&htim2, &ic, TIM_CHANNEL_4);

    TIM_OC_InitTypeDef oc = {0};
    HAL_TIM_OC_Init(&htim2);
    oc.OCMode     = TIM_OCMODE_TIMING;
    oc.Pulse      = 100;
    oc.OCPolarity = TIM_OCPOLARITY_HIGH;
    HAL_TIM_OC_ConfigChannel(&htim2, &oc, TIM_CHANNEL_3);

    HAL_NVIC_SetPriority(TIM2_IRQn, 1, 0);
    HAL_NVIC_EnableIRQ(TIM2_IRQn);
}

static void MX_TIM4_Init_10us(void)
{
    __HAL_RCC_TIM4_CLK_ENABLE();
    htim4.Instance = TIM4;
    htim4.Init.Prescaler         = 719;           /* 10us tick */
    htim4.Init.CounterMode       = TIM_COUNTERMODE_UP;
    htim4.Init.Period            = 0xFFFF;
    htim4.Init.ClockDivision     = TIM_CLOCKDIVISION_DIV1;
    htim4.Init.AutoReloadPreload = TIM_AUTORELOAD_PRELOAD_DISABLE;
    HAL_TIM_Base_Init(&htim4);
    HAL_NVIC_SetPriority(TIM4_IRQn, 2, 0);
    HAL_NVIC_EnableIRQ(TIM4_IRQn);
}

/* ========================= Error/Assert ================================== */
void Error_Handler(void)
{
  __disable_irq();
  while (1) { }
}
#ifdef  USE_FULL_ASSERT
void assert_failed(uint8_t *file, uint32_t line) { (void)file; (void)line; }
#endif
