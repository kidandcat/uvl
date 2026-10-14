/*
 * UVL on a Raspberry Pi Pico: the Lean counter app (Examples/BareMetalCounter)
 * driving an ST7789 panel. Lean renders tile N into one buffer while DMA sends
 * tile N-1 from the other; keys become UVL key events.
 */
#include <stdio.h>

#include "config.h"
#include "pico/stdlib.h"
#include "st7789.h"
#include "uvl.h"

static uint8_t tiles[2][TILE_W * TILE_H * 2];

static const struct {
    uint pin;
    uint8_t key;
} keys[] = {
    {PIN_KEY_A, UVL_KEY_UP},
    {PIN_KEY_B, UVL_KEY_DOWN},
    {PIN_KEY_X, UVL_KEY_ENTER},
    {PIN_KEY_Y, UVL_KEY_BACK},
};
#define NKEYS (sizeof keys / sizeof keys[0])

void uvl_on_panic(const char *msg, int fatal) {
    printf("uvl panic%s: %s\n", fatal ? " (fatal)" : "", msg);
    if (fatal)
        for (;;) tight_loop_contents();
}

static uvl_state draw_frame(uvl_state s) {
    s = uvl_begin_frame(s);
    int cur = 0;
    bool pending = false;
    for (uint16_t ty = 0; ty < LCD_HEIGHT; ty += TILE_H)
        for (uint16_t tx = 0; tx < LCD_WIDTH; tx += TILE_W) {
            size_t n = uvl_render_tile_rgb565(s, tx, ty, tiles[cur], sizeof tiles[cur]);
            uint16_t cw = LCD_WIDTH - tx < TILE_W ? LCD_WIDTH - tx : TILE_W;
            uint16_t ch = LCD_HEIGHT - ty < TILE_H ? LCD_HEIGHT - ty : TILE_H;
            if (pending) st7789_wait();
            st7789_blit_async(tx, ty, cw, ch, tiles[cur], n);
            pending = true;
            cur ^= 1;
        }
    if (pending) st7789_wait();
    return s;
}

int main(void) {
    stdio_init_all();
    st7789_init();
    for (unsigned i = 0; i < NKEYS; i++) {
        gpio_init(keys[i].pin);
        gpio_set_dir(keys[i].pin, GPIO_IN);
        gpio_pull_up(keys[i].pin);
    }

    uvl_rt_init();
    uvl_state s = uvl_init(LCD_WIDTH, LCD_HEIGHT, TILE_W, TILE_H);
    s = draw_frame(s);

    bool down[NKEYS] = {false};
    absolute_time_t last = get_absolute_time();
    for (;;) {
        for (unsigned i = 0; i < NKEYS; i++) {
            bool d = !gpio_get(keys[i].pin);
            if (d != down[i]) {
                s = uvl_event(s, d ? UVL_EV_KEY_DOWN : UVL_EV_KEY_UP, keys[i].key, 0);
                down[i] = d;
            }
        }
        absolute_time_t now = get_absolute_time();
        int64_t ms = absolute_time_diff_us(last, now) / 1000;
        if (ms >= 16) {
            s = uvl_event(s, UVL_EV_TICK, (uint16_t)(ms > 0xffff ? 0xffff : ms), 0);
            last = now;
        }
        if (uvl_redraw_pending(s)) {
            absolute_time_t t0 = get_absolute_time();
            s = draw_frame(s);
            uvl_heap_info h;
            uvl_heap_stats(&h);
            printf("frame %lld ms, heap live %u / peak %u B\n",
                   absolute_time_diff_us(t0, get_absolute_time()) / 1000,
                   (unsigned)h.live, (unsigned)h.peak_top);
        } else {
            sleep_ms(2);
        }
    }
}
