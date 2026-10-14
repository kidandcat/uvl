/*
 * Thin SDL3 platform shell for uvl.
 *
 * Opens a window and forwards raw input as a packed float buffer. Frames are
 * drawn by the GPU renderer (native/gpu_shell.c) on a surface made from the
 * window's native handles, or, without a usable GPU, presented as RGBA8 frames
 * rasterized by Lean through an SDL renderer. No UI logic lives here.
 *
 * Event encoding (5 doubles per event): [kind, a, b, c, d]
 *   1 move (x, y)        2 down (x, y, button)   3 up (x, y, button)
 *   4 wheel (dx, dy)     5 key down (keycode)    6 key up (keycode)
 *   7 text (codepoint)   8 resize (w, h)         9 quit     10 pointer leave
 */
#include <lean/lean.h>
#include <SDL3/SDL.h>
#include <SDL3/SDL_metal.h>
#include <webgpu/webgpu.h>
#include <stdlib.h>
#include <string.h>

/* native/gpu_shell.c */
int uvl_wgpu_init(const WGPUChainedStruct *surface_desc, const char *wgsl, const char *entries);

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
  /* the SDL renderer is only created for CPU frames (see uvl_sdl_present) */
  win = SDL_CreateWindow(lean_string_cstr(title), (int)w, (int)h, SDL_WINDOW_RESIZABLE);
  if (!win) return io_sdl_error("SDL_CreateWindow");
  SDL_StartTextInput(win);
  return io_ok();
}

/* Create the GPU renderer on the window. Returns false (and the shell falls
 * back to CPU frames) when the platform has no surface support, no GPU is
 * found, or UVL_RENDERER=cpu. */
LEAN_EXPORT lean_obj_res uvl_sdl_gpu_init(b_lean_obj_arg wgsl, b_lean_obj_arg entries,
                                          lean_obj_arg world) {
  (void)world;
  const char *force = getenv("UVL_RENDERER");
  if (!win || (force && strcmp(force, "cpu") == 0)) return lean_io_result_mk_ok(lean_box(0));
  SDL_PropertiesID props = SDL_GetWindowProperties(win);
  const char *driver = SDL_GetCurrentVideoDriver();
  const WGPUChainedStruct *chain = NULL;
  WGPUSurfaceSourceXlibWindow xlib = {.chain = {.sType = WGPUSType_SurfaceSourceXlibWindow}};
  WGPUSurfaceSourceWaylandSurface wl = {.chain = {.sType = WGPUSType_SurfaceSourceWaylandSurface}};
  WGPUSurfaceSourceMetalLayer metal = {.chain = {.sType = WGPUSType_SurfaceSourceMetalLayer}};
  WGPUSurfaceSourceWindowsHWND hwnd = {.chain = {.sType = WGPUSType_SurfaceSourceWindowsHWND}};
  if (driver && strcmp(driver, "x11") == 0) {
    xlib.display = SDL_GetPointerProperty(props, SDL_PROP_WINDOW_X11_DISPLAY_POINTER, NULL);
    xlib.window = (uint64_t)SDL_GetNumberProperty(props, SDL_PROP_WINDOW_X11_WINDOW_NUMBER, 0);
    if (xlib.display && xlib.window) chain = &xlib.chain;
  } else if (driver && strcmp(driver, "wayland") == 0) {
    wl.display = SDL_GetPointerProperty(props, SDL_PROP_WINDOW_WAYLAND_DISPLAY_POINTER, NULL);
    wl.surface = SDL_GetPointerProperty(props, SDL_PROP_WINDOW_WAYLAND_SURFACE_POINTER, NULL);
    if (wl.display && wl.surface) chain = &wl.chain;
  } else if (driver && strcmp(driver, "cocoa") == 0) {
    SDL_MetalView view = SDL_Metal_CreateView(win);
    metal.layer = view ? SDL_Metal_GetLayer(view) : NULL;
    if (metal.layer) chain = &metal.chain;
  } else if (driver && strcmp(driver, "windows") == 0) {
    hwnd.hwnd = SDL_GetPointerProperty(props, SDL_PROP_WINDOW_WIN32_HWND_POINTER, NULL);
    hwnd.hinstance = SDL_GetPointerProperty(props, SDL_PROP_WINDOW_WIN32_INSTANCE_POINTER, NULL);
    if (hwnd.hwnd) chain = &hwnd.chain;
  }
  int ok = chain && uvl_wgpu_init(chain, lean_string_cstr(wgsl), lean_string_cstr(entries));
  return lean_io_result_mk_ok(lean_box(ok ? 1 : 0));
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
      /* notches to pixels, positive = scroll down (Event.scroll) */
      arr = push(arr, 4, -40.0 * e.wheel.x, -40.0 * e.wheel.y, 0); break;
    case SDL_EVENT_KEY_DOWN:
      if (e.key.key == SDLK_V && (e.key.mod & (SDL_KMOD_CTRL | SDL_KMOD_GUI))) {
        /* paste: the clipboard text arrives as text input */
        char *text = SDL_GetClipboardText();
        const char *s = text;
        uint32_t cp; int n;
        while (s && (n = utf8_next(s, &cp)) > 0) { arr = push(arr, 7, cp, 0, 0); s += n; }
        SDL_free(text);
        break;
      }
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

LEAN_EXPORT lean_obj_res uvl_sdl_set_clipboard(b_lean_obj_arg text, lean_obj_arg world) {
  SDL_SetClipboardText(lean_string_cstr(text));
  return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res uvl_sdl_present(b_lean_obj_arg rgba, uint32_t w, uint32_t h,
                                         lean_obj_arg world) {
  (void)world;
  if (!win) return io_sdl_error("present before open");
  if (!ren) {
    ren = SDL_CreateRenderer(win, NULL);
    if (!ren) return io_sdl_error("SDL_CreateRenderer");
    SDL_SetRenderVSync(ren, 1);
  }
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
