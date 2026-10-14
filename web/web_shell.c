/*
 * Browser shell: the C side of the WebAssembly build.
 *
 * JavaScript (web/uvl.js) owns the requestAnimationFrame loop, DOM events and
 * the WebGPU presenter. Each frame it packs pending input into a Float64Array
 * (5 doubles per event, same encoding as the SDL shell, see
 * UVL/App/Host.lean) and calls `uvl_step`. When that returns 1 there
 * is a new RGBA frame at `uvl_frame_ptr()`, of which only the
 * `uvl_damage_count()` windows at `uvl_damage_ptr()` (x, y, w, h doubles)
 * changed since the previous one.
 *
 * Everything else, state, layout, hit testing and rasterization, is Lean.
 */
#include <lean/lean.h>
#include <emscripten.h>
#include <string.h>

/* The app's module initializer and constructor (overridden by web/build.sh). */
#ifndef UVL_WEB_INIT
#define UVL_WEB_INIT initialize_uvl_Examples_CounterWeb
#endif
extern lean_object *UVL_WEB_INIT(uint8_t builtin);
extern lean_object *uvl_web_make(uint32_t w, uint32_t h);

/* UVL.AnyRuntime exports; every argument is owned. */
extern lean_object *uvl_host_step(lean_object *r, lean_object *raw, double dt_ms);
extern uint8_t uvl_host_dirty(lean_object *r);
extern uint8_t uvl_host_quit(lean_object *r);
extern uint32_t uvl_host_width(lean_object *r);
extern uint32_t uvl_host_height(lean_object *r);
extern lean_object *uvl_host_present(lean_object *r);
extern lean_object *uvl_host_pixels(lean_object *r);
extern lean_object *uvl_host_damage(lean_object *r);
extern lean_object *uvl_host_target_center(lean_object *r, uint32_t i);

extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);

static lean_object *g_rt = NULL;    /* current AnyRuntime */
static uint8_t *g_pixels = NULL;     /* RGBA of the last present, owned by g_rt */
static double g_damage[4 * 16];      /* windows repainted by the last present */
static uint32_t g_ndamage = 0;
static double g_target[2];

EMSCRIPTEN_KEEPALIVE int uvl_init(uint32_t w, uint32_t h) {
  lean_initialize_runtime_module();
  lean_object *res = UVL_WEB_INIT(1);
  if (!lean_io_result_is_ok(res)) {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 0;
  }
  lean_dec_ref(res);
  lean_io_mark_end_initialization();
  g_rt = uvl_web_make(w, h);
  return 1;
}

/* Apply `n` packed events from `events` (5 doubles each) and advance
 * animations by `dt_ms`. Returns 1 when a new frame was rendered, 2 when the
 * app asked to quit, 0 otherwise. */
EMSCRIPTEN_KEEPALIVE int uvl_step(const double *events, uint32_t n, double dt_ms) {
  lean_object *raw = lean_alloc_sarray(sizeof(double), 5 * n, 5 * n);
  memcpy(lean_float_array_cptr(raw), events, sizeof(double) * 5 * n);
  g_rt = uvl_host_step(g_rt, raw, dt_ms);
  lean_inc(g_rt);
  if (uvl_host_quit(g_rt)) return 2;
  lean_inc(g_rt);
  if (!uvl_host_dirty(g_rt)) return 0;
  /* g_rt is the only reference here, so the frame is repainted in place */
  g_rt = uvl_host_present(g_rt);
  lean_inc(g_rt);
  lean_object *px = uvl_host_pixels(g_rt);
  g_pixels = lean_sarray_size(px) ? lean_sarray_cptr(px) : NULL;
  lean_dec_ref(px); /* still alive: g_rt holds it */
  lean_inc(g_rt);
  lean_object *dmg = uvl_host_damage(g_rt);
  size_t nd = lean_sarray_size(dmg) / 4;
  if (nd > 16) nd = 16;
  memcpy(g_damage, lean_float_array_cptr(dmg), sizeof(double) * 4 * nd);
  g_ndamage = (uint32_t)nd;
  lean_dec_ref(dmg);
  return 1;
}

EMSCRIPTEN_KEEPALIVE uint8_t *uvl_frame_ptr(void) { return g_pixels; }
EMSCRIPTEN_KEEPALIVE double *uvl_damage_ptr(void) { return g_damage; }
EMSCRIPTEN_KEEPALIVE uint32_t uvl_damage_count(void) { return g_ndamage; }

EMSCRIPTEN_KEEPALIVE uint32_t uvl_width(void) { lean_inc(g_rt); return uvl_host_width(g_rt); }
EMSCRIPTEN_KEEPALIVE uint32_t uvl_height(void) { lean_inc(g_rt); return uvl_host_height(g_rt); }

/* Centre of tap target `i` as two doubles, or NULL (for smoke tests). */
EMSCRIPTEN_KEEPALIVE double *uvl_target_center(uint32_t i) {
  lean_inc(g_rt);
  lean_object *a = uvl_host_target_center(g_rt, i);
  double *p = NULL;
  if (lean_sarray_size(a) == 2) {
    memcpy(g_target, lean_float_array_cptr(a), sizeof g_target);
    p = g_target;
  }
  lean_dec_ref(a);
  return p;
}
