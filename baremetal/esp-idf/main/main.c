/*
 * UVL on an ESP32: the Lean counter app (Examples/BareMetalCounter) driving an
 * ST7789 panel through esp_lcd. Two DMA-capable tile buffers: Lean renders
 * into one while the SPI driver sends the other.
 */
#include <stdio.h>

#include "config.h"
#include "driver/gpio.h"
#include "driver/spi_master.h"
#include "esp_heap_caps.h"
#include "esp_lcd_panel_io.h"
#include "esp_lcd_panel_ops.h"
#include "esp_lcd_panel_st7789.h"
#include "esp_timer.h"
#include "freertos/FreeRTOS.h"
#include "freertos/semphr.h"
#include "freertos/task.h"
#include "uvl.h"

static esp_lcd_panel_handle_t panel;
static SemaphoreHandle_t free_buffers; /* counts tile buffers not owned by DMA */
static uint8_t *tiles[2];

static const struct {
    gpio_num_t pin;
    uint8_t key;
} keys[] = {KEYS};
#define NKEYS (sizeof keys / sizeof keys[0])

void uvl_on_panic(const char *msg, int fatal) {
    printf("uvl panic%s: %s\n", fatal ? " (fatal)" : "", msg);
    if (fatal) abort();
}

static bool on_trans_done(esp_lcd_panel_io_handle_t io, esp_lcd_panel_io_event_data_t *ev, void *ctx) {
    BaseType_t woken = pdFALSE;
    xSemaphoreGiveFromISR(free_buffers, &woken);
    return woken == pdTRUE;
}

static void lcd_init(void) {
    spi_bus_config_t bus = {
        .sclk_io_num = PIN_LCD_SCLK,
        .mosi_io_num = PIN_LCD_MOSI,
        .miso_io_num = -1,
        .quadwp_io_num = -1,
        .quadhd_io_num = -1,
        .max_transfer_sz = TILE_W * TILE_H * 2,
    };
    ESP_ERROR_CHECK(spi_bus_initialize(LCD_HOST, &bus, SPI_DMA_CH_AUTO));

    esp_lcd_panel_io_handle_t io;
    esp_lcd_panel_io_spi_config_t io_cfg = {
        .dc_gpio_num = PIN_LCD_DC,
        .cs_gpio_num = PIN_LCD_CS,
        .pclk_hz = LCD_PIXEL_CLOCK_HZ,
        .lcd_cmd_bits = 8,
        .lcd_param_bits = 8,
        .spi_mode = 0,
        .trans_queue_depth = 2,
        .on_color_trans_done = on_trans_done,
    };
    ESP_ERROR_CHECK(esp_lcd_new_panel_io_spi((esp_lcd_spi_bus_handle_t)LCD_HOST, &io_cfg, &io));

    esp_lcd_panel_dev_config_t dev = {
        .reset_gpio_num = PIN_LCD_RST,
        .rgb_ele_order = LCD_RGB_ELEMENT_ORDER_RGB,
        .bits_per_pixel = 16,
    };
    ESP_ERROR_CHECK(esp_lcd_new_panel_st7789(io, &dev, &panel));
    ESP_ERROR_CHECK(esp_lcd_panel_reset(panel));
    ESP_ERROR_CHECK(esp_lcd_panel_init(panel));
    ESP_ERROR_CHECK(esp_lcd_panel_invert_color(panel, LCD_INVERT));
    ESP_ERROR_CHECK(esp_lcd_panel_swap_xy(panel, LCD_SWAP_XY));
    ESP_ERROR_CHECK(esp_lcd_panel_mirror(panel, LCD_MIRROR_X, LCD_MIRROR_Y));
    ESP_ERROR_CHECK(esp_lcd_panel_set_gap(panel, LCD_GAP_X, LCD_GAP_Y));
    ESP_ERROR_CHECK(esp_lcd_panel_disp_on_off(panel, true));

    gpio_set_direction(PIN_LCD_BL, GPIO_MODE_OUTPUT);
    gpio_set_level(PIN_LCD_BL, 1);
}

static uvl_state draw_frame(uvl_state s) {
    s = uvl_begin_frame(s);
    int cur = 0;
    for (int ty = 0; ty < LCD_HEIGHT; ty += TILE_H)
        for (int tx = 0; tx < LCD_WIDTH; tx += TILE_W) {
            xSemaphoreTake(free_buffers, portMAX_DELAY); /* tiles[cur] is no longer in flight */
            uvl_render_tile_rgb565(s, tx, ty, tiles[cur], TILE_W * TILE_H * 2);
            int cw = LCD_WIDTH - tx < TILE_W ? LCD_WIDTH - tx : TILE_W;
            int ch = LCD_HEIGHT - ty < TILE_H ? LCD_HEIGHT - ty : TILE_H;
            ESP_ERROR_CHECK(esp_lcd_panel_draw_bitmap(panel, tx, ty, tx + cw, ty + ch, tiles[cur]));
            cur ^= 1;
        }
    /* Wait for both buffers to come back before the next frame reuses them. */
    xSemaphoreTake(free_buffers, portMAX_DELAY);
    xSemaphoreTake(free_buffers, portMAX_DELAY);
    xSemaphoreGive(free_buffers);
    xSemaphoreGive(free_buffers);
    return s;
}

void app_main(void) {
    free_buffers = xSemaphoreCreateCounting(2, 2);
    for (int i = 0; i < 2; i++) tiles[i] = heap_caps_malloc(TILE_W * TILE_H * 2, MALLOC_CAP_DMA);
    lcd_init();
    for (unsigned i = 0; i < NKEYS; i++) {
        gpio_set_direction(keys[i].pin, GPIO_MODE_INPUT);
        if (GPIO_IS_VALID_OUTPUT_GPIO(keys[i].pin)) gpio_set_pull_mode(keys[i].pin, GPIO_PULLUP_ONLY);
    }

    uvl_rt_init();
    uvl_state s = uvl_init(LCD_WIDTH, LCD_HEIGHT, TILE_W, TILE_H);
    int64_t t0 = esp_timer_get_time();
    s = draw_frame(s);
    printf("uvl: %dx%d, first frame %lld ms\n", LCD_WIDTH, LCD_HEIGHT, (esp_timer_get_time() - t0) / 1000);

    bool down[NKEYS] = {false};
    int64_t last = esp_timer_get_time();
    for (;;) {
        for (unsigned i = 0; i < NKEYS; i++) {
            bool d = gpio_get_level(keys[i].pin) == 0;
            if (d != down[i]) {
                s = uvl_event(s, d ? UVL_EV_KEY_DOWN : UVL_EV_KEY_UP, keys[i].key, 0);
                down[i] = d;
            }
        }
        int64_t now = esp_timer_get_time();
        int64_t ms = (now - last) / 1000;
        if (ms >= 16) {
            s = uvl_event(s, UVL_EV_TICK, ms > 0xffff ? 0xffff : (uint16_t)ms, 0);
            last = now;
        }
        if (uvl_redraw_pending(s)) {
            int64_t t0 = esp_timer_get_time();
            s = draw_frame(s);
            uvl_heap_info h;
            uvl_heap_stats(&h);
            printf("frame %lld ms, heap live %u / peak %u B\n", (now = esp_timer_get_time(), (now - t0) / 1000),
                   (unsigned)h.live, (unsigned)h.peak_top);
        } else {
            vTaskDelay(pdMS_TO_TICKS(5));
        }
    }
}
