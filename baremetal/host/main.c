/*
 * Host harness for the bare-metal build: runs the *same* C bundle that goes on
 * the microcontroller (generated Lean C + uvl_rt.c, no libleanrt) on a PC.
 *
 *   uvl-host [out-dir] [extra-frames]
 *
 * Streams frames tile by tile exactly like the firmware loop, assembles them
 * into row-major RGB565 files (frame0.rgb565, frame1.rgb565) and prints the
 * pool statistics. tools/host_test.sh compares the files with the frames the
 * native Lean build produces.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "uvl.h"

#define W 320
#define H 240
#define TW 64
#define TH 16

static uint8_t frame[W * H * 2];
static uint8_t tile[TW * TH * 2];

void uvl_on_panic(const char *msg, int fatal) {
    fprintf(stderr, "uvl panic%s: %s\n", fatal ? " (fatal)" : "", msg);
    if (fatal) exit(2);
}

static uvl_state stream_frame(uvl_state s, const char *path) {
    s = uvl_begin_frame(s);
    for (int ty = 0; ty < H; ty += TH)
        for (int tx = 0; tx < W; tx += TW) {
            size_t n = uvl_render_tile_rgb565(s, tx, ty, tile, sizeof tile);
            int cw = W - tx < TW ? W - tx : TW;
            int ch = H - ty < TH ? H - ty : TH;
            if (n != (size_t)(cw * ch * 2)) { fprintf(stderr, "bad tile size %lu\n", (unsigned long)n); exit(1); }
            for (int row = 0; row < ch; row++)
                memcpy(frame + ((ty + row) * W + tx) * 2, tile + row * cw * 2, cw * 2);
        }
    FILE *f = fopen(path, "wb");
    if (!f) { perror(path); exit(1); }
    fwrite(frame, 1, sizeof frame, f);
    fclose(f);
    return s;
}

static void stats(const char *when) {
    uvl_heap_info h;
    uvl_heap_stats(&h);
    printf("%-18s live %6lu B  peak live %6lu B  pool high-water %6lu / %lu B  allocs %lu  defrag %lu\n",
           when, (unsigned long)h.live, (unsigned long)h.peak_live, (unsigned long)h.peak_top,
           (unsigned long)h.capacity, (unsigned long)h.allocations, (unsigned long)h.coalesces);
}

int main(int argc, char **argv) {
    const char *dir = argc > 1 ? argv[1] : ".";
    int extra = argc > 2 ? atoi(argv[2]) : 20;
    char path[512];
    uvl_rt_init();
    stats("after init");
    uvl_state s = uvl_init(W, H, TW, TH);
    stats("after uvl_init");
    snprintf(path, sizeof path, "%s/frame0.rgb565", dir);
    s = stream_frame(s, path);
    stats("after frame 0");
    /* the same script as Examples/BareMetalRef.lean */
    s = uvl_event(s, UVL_EV_KEY_DOWN, UVL_KEY_UP, 0);
    s = uvl_event(s, UVL_EV_KEY_DOWN, UVL_KEY_UP, 0);
    s = uvl_event(s, UVL_EV_KEY_DOWN, UVL_KEY_UP, 0);
    s = uvl_event(s, UVL_EV_KEY_DOWN, UVL_KEY_DOWN, 0);
    s = uvl_event(s, UVL_EV_POINTER_MOVE, 30, 200);
    if (!uvl_redraw_pending(s)) { fprintf(stderr, "expected a redraw\n"); return 1; }
    snprintf(path, sizeof path, "%s/frame1.rgb565", dir);
    s = stream_frame(s, path);
    stats("after frame 1");
    /* steady state: many frames must not grow the pool */
    for (int i = 0; i < extra; i++) {
        s = uvl_event(s, UVL_EV_KEY_DOWN, i % 3 ? UVL_KEY_UP : UVL_KEY_DOWN, 0);
        snprintf(path, sizeof path, "%s/scratch.rgb565", dir);
        s = stream_frame(s, path);
    }
    printf("(%d more frames)\n", extra);
    stats("after more frames");
    uvl_state_free(s);
    stats("after free");
    return 0;
}
