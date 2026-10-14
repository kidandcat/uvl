/*
 * uvl.h: C interface between a microcontroller main loop and a UVL app
 * compiled from Lean (see Examples/BareMetalCounter.lean for the exports).
 *
 * Lean never touches the hardware. The firmware owns SPI/I2C/GPIO/DMA and asks
 * Lean to (1) fold input events into the UI state and (2) render the current
 * frame one small tile at a time:
 *
 *     uvl_rt_init();
 *     uvl_state s = uvl_init(W, H, TILE_W, TILE_H);
 *     for (;;) {
 *         s = uvl_event(s, UVL_EV_KEY_DOWN, UVL_KEY_UP, 0);   // from buttons/touch
 *         if (uvl_needs_redraw(s)) {
 *             s = uvl_begin_frame(s);
 *             for (ty = 0; ty < H; ty += TILE_H)
 *                 for (tx = 0; tx < W; tx += TILE_W)
 *                     n = uvl_render_tile_rgb565(s, tx, ty, dma_buf[i ^= 1], sizeof dma_buf[0]);
 *                     // start the DMA transfer of dma_buf[i] while Lean renders the next tile
 *         }
 *     }
 *
 * Ownership follows Lean's calling convention: `uvl_event` and
 * `uvl_begin_frame` consume their state argument and return the new one; the
 * `uvl_render_tile_*` / `uvl_redraw` wrappers below borrow it.
 */
#ifndef UVL_H
#define UVL_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* A Lean object (`BareMetal.Shell`), opaque to C. */
typedef void *uvl_state;

/* Event kinds (`kind` argument of uvl_event). */
enum {
    UVL_EV_NONE = 0,
    UVL_EV_POINTER_DOWN = 1, /* a = x, b = y (pixels) */
    UVL_EV_POINTER_MOVE = 2,
    UVL_EV_POINTER_UP = 3,
    UVL_EV_KEY_DOWN = 4,     /* a = key code */
    UVL_EV_KEY_UP = 5,
    UVL_EV_TICK = 6          /* a = elapsed milliseconds */
};

/* Key codes; codes >= 32 are characters. */
enum {
    UVL_KEY_UP = 1, UVL_KEY_DOWN = 2, UVL_KEY_LEFT = 3, UVL_KEY_RIGHT = 4,
    UVL_KEY_ENTER = 5, UVL_KEY_BACK = 6
};

/* ---- Exported from Lean (@[export]) ------------------------------------ */

uvl_state uvl_init(uint16_t width, uint16_t height, uint16_t tile_w, uint16_t tile_h);
uvl_state uvl_event(uvl_state s, uint8_t kind, uint16_t a, uint16_t b);
uint8_t uvl_needs_redraw(uvl_state s);                 /* consumes s */
uvl_state uvl_begin_frame(uvl_state s);
void *uvl_tile_rgb565(uvl_state s, uint16_t tx, uint16_t ty); /* consumes s */
void *uvl_tile_mono(uvl_state s, uint16_t tx, uint16_t ty);   /* consumes s */

/* ---- Provided by uvl_rt.c / generated uvl_init.c ----------------------- */

/* Initialize the closed constants the app needs (call once, before uvl_init). */
void uvl_rt_init(void);

/* Borrowing wrappers: copy the tile into `out` (big-endian RGB565, or
   SSD1306 pages) and return the number of bytes written. */
size_t uvl_render_tile_rgb565(uvl_state s, uint16_t tx, uint16_t ty, uint8_t *out, size_t cap);
size_t uvl_render_tile_mono(uvl_state s, uint16_t tx, uint16_t ty, uint8_t *out, size_t cap);
int uvl_redraw_pending(uvl_state s);

/* Release a state you no longer need. */
void uvl_state_free(uvl_state s);

typedef struct {
    size_t capacity;    /* UVL_HEAP_SIZE */
    size_t live;        /* bytes currently allocated */
    size_t peak_live;   /* high-water mark of live bytes */
    size_t peak_top;    /* high-water mark of the pool (fragmentation included) */
    size_t allocations; /* total number of allocations */
    size_t coalesces;   /* times the pool was defragmented */
} uvl_heap_info;

void uvl_heap_stats(uvl_heap_info *out);

/* Called on Lean panics (fatal = 0: the program continues with a default
   value) and on fatal runtime errors (fatal = 1: must not return). Weak
   default: ignore / spin. Override it to log over UART or blink an LED. */
void uvl_on_panic(const char *msg, int fatal);

#ifdef __cplusplus
}
#endif

#endif
