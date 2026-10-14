/*
 * Thin SDL3 platform shell for uvl.
 *
 * Opens a window, forwards raw input as a packed float buffer and presents an
 * RGBA8 frame produced by the Lean runtime. No UI logic lives here.
 *
 * Event encoding (5 doubles per event): [kind, a, b, c, d]
 *   1 move (x, y)        2 down (x, y, button)   3 up (x, y, button)
 *   4 wheel (dx, dy)     5 key down (keycode)    6 key up (keycode)
 *   7 text (codepoint)   8 resize (w, h)         9 quit     10 pointer leave
 */
#include <lean/lean.h>
#include <SDL3/SDL.h>

static SDL_Window *win = NULL;
static SDL_Renderer *ren = NULL;
static SDL_Texture *tex = NULL;
static int tex_w = 0, tex_h = 0;

static lean_obj_res io_ok(void) { return lean_io_result_mk_ok(lean_box(0)); }

static lean_obj_res io_sdl_error(const char *what) {
  char buf[512];
  SDL_snprintf(buf, sizeof buf, "%s: %s", what, SDL_GetError());
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

LEAN_EXPORT lean_obj_res uvl_sdl_open(b_lean_obj_arg title, uint32_t w, uint32_t h,
                                      lean_obj_arg world) {
  (void)world;
  if (!SDL_Init(SDL_INIT_VIDEO)) return io_sdl_error("SDL_Init");
  if (!SDL_CreateWindowAndRenderer(lean_string_cstr(title), (int)w, (int)h,
                                   SDL_WINDOW_RESIZABLE, &win, &ren))
    return io_sdl_error("SDL_CreateWindowAndRenderer");
  SDL_SetRenderVSync(ren, 1);
  SDL_StartTextInput(win);
  return io_ok();
}

static lean_obj_res push(lean_obj_res arr, double k, double a, double b, double c) {
  arr = lean_float_array_push(arr, k);
  arr = lean_float_array_push(arr, a);
  arr = lean_float_array_push(arr, b);
  arr = lean_float_array_push(arr, c);
  return lean_float_array_push(arr, 0.0);
}

/* Decode one UTF-8 code point; returns bytes consumed (0 at end). */
static int utf8_next(const unsigned char *s, uint32_t *cp) {
  if (!s[0]) return 0;
  if (s[0] < 0x80) { *cp = s[0]; return 1; }
  if ((s[0] & 0xE0) == 0xC0 && s[1]) { *cp = ((s[0] & 0x1F) << 6) | (s[1] & 0x3F); return 2; }
  if ((s[0] & 0xF0) == 0xE0 && s[1] && s[2]) {
    *cp = ((s[0] & 0x0F) << 12) | ((s[1] & 0x3F) << 6) | (s[2] & 0x3F); return 3;
  }
  if (s[1] && s[2] && s[3]) {
    *cp = ((s[0] & 0x07) << 18) | ((s[1] & 0x3F) << 12) | ((s[2] & 0x3F) << 6) | (s[3] & 0x3F);
    return 4;
  }
  *cp = 0xFFFD; return 1;
}

LEAN_EXPORT lean_obj_res uvl_sdl_poll(lean_obj_arg world) {
  (void)world;
  lean_obj_res arr = lean_mk_empty_float_array(lean_box(64));
  SDL_Event e;
  while (SDL_PollEvent(&e)) {
    switch (e.type) {
    case SDL_EVENT_MOUSE_MOTION:
      arr = push(arr, 1, e.motion.x, e.motion.y, 0); break;
    case SDL_EVENT_MOUSE_BUTTON_DOWN:
      arr = push(arr, 2, e.button.x, e.button.y, e.button.button); break;
    case SDL_EVENT_MOUSE_BUTTON_UP:
      arr = push(arr, 3, e.button.x, e.button.y, e.button.button); break;
    case SDL_EVENT_MOUSE_WHEEL:
      arr = push(arr, 4, e.wheel.x, e.wheel.y, 0); break;
    case SDL_EVENT_KEY_DOWN:
      arr = push(arr, 5, (double)e.key.key, 0, 0); break;
    case SDL_EVENT_KEY_UP:
      arr = push(arr, 6, (double)e.key.key, 0, 0); break;
    case SDL_EVENT_TEXT_INPUT: {
      const unsigned char *s = (const unsigned char *)e.text.text;
      uint32_t cp; int n;
      while ((n = utf8_next(s, &cp)) > 0) { arr = push(arr, 7, cp, 0, 0); s += n; }
      break;
    }
    case SDL_EVENT_WINDOW_PIXEL_SIZE_CHANGED:
      arr = push(arr, 8, e.window.data1, e.window.data2, 0); break;
    case SDL_EVENT_WINDOW_MOUSE_LEAVE:
      arr = push(arr, 10, 0, 0, 0); break;
    case SDL_EVENT_QUIT:
      arr = push(arr, 9, 0, 0, 0); break;
    default: break;
    }
  }
  return lean_io_result_mk_ok(arr);
}

LEAN_EXPORT lean_obj_res uvl_sdl_present(b_lean_obj_arg rgba, uint32_t w, uint32_t h,
                                         lean_obj_arg world) {
  (void)world;
  if (!ren) return io_sdl_error("present before open");
  if (lean_sarray_size(rgba) < (size_t)w * h * 4) return io_sdl_error("frame too small");
  if (!tex || tex_w != (int)w || tex_h != (int)h) {
    if (tex) SDL_DestroyTexture(tex);
    tex = SDL_CreateTexture(ren, SDL_PIXELFORMAT_RGBA32, SDL_TEXTUREACCESS_STREAMING,
                            (int)w, (int)h);
    if (!tex) return io_sdl_error("SDL_CreateTexture");
    tex_w = (int)w; tex_h = (int)h;
  }
  SDL_UpdateTexture(tex, NULL, lean_sarray_cptr(rgba), (int)w * 4);
  SDL_RenderClear(ren);
  SDL_RenderTexture(ren, tex, NULL, NULL);
  SDL_RenderPresent(ren);
  return io_ok();
}

LEAN_EXPORT lean_obj_res uvl_sdl_wait(uint32_t timeout_ms, lean_obj_arg world) {
  (void)world;
  SDL_WaitEventTimeout(NULL, (Sint32)timeout_ms);
  return io_ok();
}

LEAN_EXPORT lean_obj_res uvl_sdl_ticks(lean_obj_arg world) {
  (void)world;
  return lean_io_result_mk_ok(lean_box_uint64(SDL_GetTicks()));
}

LEAN_EXPORT lean_obj_res uvl_sdl_close(lean_obj_arg world) {
  (void)world;
  if (tex) SDL_DestroyTexture(tex);
  if (ren) SDL_DestroyRenderer(ren);
  if (win) SDL_DestroyWindow(win);
  tex = NULL; ren = NULL; win = NULL;
  SDL_Quit();
  return io_ok();
}

/* Inject a synthetic left click through SDL's own event queue (smoke tests). */
LEAN_EXPORT lean_obj_res uvl_sdl_push_click(double x, double y, lean_obj_arg world) {
  (void)world;
  SDL_Event e;
  SDL_zero(e);
  e.type = SDL_EVENT_MOUSE_MOTION;
  e.motion.x = (float)x; e.motion.y = (float)y;
  SDL_PushEvent(&e);
  SDL_zero(e);
  e.type = SDL_EVENT_MOUSE_BUTTON_DOWN;
  e.button.button = SDL_BUTTON_LEFT; e.button.down = true;
  e.button.x = (float)x; e.button.y = (float)y;
  SDL_PushEvent(&e);
  e.type = SDL_EVENT_MOUSE_BUTTON_UP;
  e.button.down = false;
  SDL_PushEvent(&e);
  return io_ok();
}
