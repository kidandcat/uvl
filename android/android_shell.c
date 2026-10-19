/*
 * Android shell: a NativeActivity (no Java/Kotlin code in the APK) that runs a
 * UVL app.
 *
 * Like the other shells it only moves events in and pixels out: touches and
 * keys become packed events (5 doubles each, see UVL/App/Host.lean) for
 * `uvl_host_step`, and when the runtime has a new frame its RGBA pixels are
 * copied into the window. Layout, hit testing, text and rasterization are Lean.
 *
 * The app renders at "density-independent" resolution: the window buffer is
 * the surface size divided by the display density (e.g. 1080x2400 at 420 dpi
 * becomes 411x914), and the compositor scales it up. That keeps the CPU
 * rasterizer fast and makes the UI as large on a phone as on a desktop.
 *
 * The on-screen keyboard is shown while a text input has the focus
 * (`uvl_host_text_focus`); typed characters are decoded with the framework's
 * `KeyEvent.getUnicodeChar` through JNI.
 *
 * When the app imports UVLGPU, android/build.sh also links the WebGPU renderer
 * (native/gpu_shell.c on wgpu-native) and frames are drawn on the window's
 * Vulkan surface; the CPU rasterizer is the fallback when the GPU cannot start,
 * or with `adb shell setprop debug.uvl.cpu 1`. `debug.uvl.present` (immediate,
 * mailbox) selects the present mode like UVL_PRESENT on desktop.
 *
 * For measuring, `adb shell setprop debug.uvl.stats 1` (read at launch) makes
 * the loop log the frame rate and the time per frame spent stepping the
 * runtime (update, view, layout) and presenting (CPU: rasterize and copy;
 * GPU: lower, upload and draw), every two seconds.
 */
#include <android/configuration.h>
#include <android/input.h>
#include <android/keycodes.h>
#include <android/log.h>
#include <android/looper.h>
#include <android/native_activity.h>
#include <android/native_window.h>
#include <android_native_app_glue.h>
#include <jni.h>
#include <lean/lean.h>
#include <pthread.h>
#include <stdlib.h>
#include <string.h>
#include <sys/system_properties.h>
#include <time.h>
#ifdef UVL_ANDROID_GPU
#include <webgpu/webgpu.h>
#endif

#define LOG(...) __android_log_print(ANDROID_LOG_INFO, "uvl", __VA_ARGS__)

/* The app's module initializer (set by android/build.sh) and constructor. */
#ifndef UVL_ANDROID_INIT
#define UVL_ANDROID_INIT initialize_uvl_Examples_PhoneAndroid
#endif
extern lean_object *UVL_ANDROID_INIT(uint8_t builtin);
extern lean_object *uvl_android_make(uint32_t w, uint32_t h);

/* UVL.AnyRuntime exports; every argument is owned. */
extern lean_object *uvl_host_step(lean_object *r, lean_object *raw, double dt_ms);
extern uint8_t uvl_host_dirty(lean_object *r);
extern uint8_t uvl_host_quit(lean_object *r);
extern uint8_t uvl_host_animating(lean_object *r);
extern uint8_t uvl_host_text_focus(lean_object *r);
extern uint32_t uvl_host_width(lean_object *r);
extern uint32_t uvl_host_height(lean_object *r);
extern lean_object *uvl_host_present(lean_object *r);
extern lean_object *uvl_host_pixels(lean_object *r);
extern lean_object *uvl_host_invalidate(lean_object *r);
extern lean_object *uvl_host_background(lean_object *r);

extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);

enum { EV_MOVE = 1, EV_DOWN = 2, EV_UP = 3, EV_KEY_DOWN = 5, EV_KEY_UP = 6, EV_TEXT = 7,
       EV_RESIZE = 8, EV_LEAVE = 10, EV_TOUCH_DOWN = 13, EV_TOUCH_MOVE = 14,
       EV_TOUCH_UP = 15 };

/* SDL keycodes, as UVL/App/Host.lean decodes them. */
#define K_RIGHT 0x4000004F
#define K_LEFT 0x40000050
#define K_DOWN 0x40000051
#define K_UP 0x40000052
#define K_HOME 0x4000004A
#define K_END 0x4000004D
#define K_SHIFT 0x400000E1
#define K_CTRL 0x400000E0

typedef struct {
  struct android_app *app;
  lean_object *rt;      /* current AnyRuntime, survives activity restarts */
  int32_t bw, bh;       /* window buffer size (logical pixels) */
  int32_t ox, oy, lw, lh; /* the app's rectangle in the buffer */
  float sx, sy;         /* screen pixels -> logical pixels */
  int has_window, visible, keyboard;
  double events[5 * 256];
  uint32_t nevents;
  JNIEnv *env;
  jclass key_event;
  jmethodID key_event_new, key_event_unicode;
} shell;

static shell g;

static void push(int kind, double a, double b, double c) {
  if (g.nevents == 256) return; /* dropped; the queue is drained every iteration */
  double *e = &g.events[5 * g.nevents++];
  e[0] = kind; e[1] = a; e[2] = b; e[3] = c; e[4] = 0;
}

static double now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1e3 + ts.tv_nsec / 1e6;
}

/* --- JNI helpers ----------------------------------------------------------- */

static int check_exception(void) {
  if ((*g.env)->ExceptionCheck(g.env)) {
    (*g.env)->ExceptionClear(g.env);
    return 1;
  }
  return 0;
}

/* The character a key event types, or 0. */
static uint32_t unicode_of(AInputEvent *ev) {
  JNIEnv *env = g.env;
  if (!g.key_event) {
    jclass c = (*env)->FindClass(env, "android/view/KeyEvent");
    if (check_exception() || !c) return 0;
    g.key_event = (*env)->NewGlobalRef(env, c);
    g.key_event_new = (*env)->GetMethodID(env, c, "<init>", "(II)V");
    g.key_event_unicode = (*env)->GetMethodID(env, c, "getUnicodeChar", "(I)I");
    (*env)->DeleteLocalRef(env, c);
  }
  jobject k = (*env)->NewObject(env, g.key_event, g.key_event_new, AKeyEvent_getAction(ev),
                                AKeyEvent_getKeyCode(ev));
  if (check_exception() || !k) return 0;
  jint c = (*env)->CallIntMethod(env, k, g.key_event_unicode, AKeyEvent_getMetaState(ev));
  (*env)->DeleteLocalRef(env, k);
  if (check_exception() || c <= 0 || (c & 0x80000000)) return 0; /* COMBINING_ACCENT */
  return (uint32_t)c;
}

/* Show or hide the soft keyboard through InputMethodManager (the NDK's
 * ANativeActivity_showSoftInput is ignored by many devices). */
static void set_keyboard(int show) {
  if (g.keyboard == show) return;
  g.keyboard = show;
  JNIEnv *env = g.env;
  jobject activity = g.app->activity->clazz;
  jclass ctx = (*env)->FindClass(env, "android/content/Context");
  jfieldID f = (*env)->GetStaticFieldID(env, ctx, "INPUT_METHOD_SERVICE", "Ljava/lang/String;");
  jobject name = (*env)->GetStaticObjectField(env, ctx, f);
  jclass act = (*env)->GetObjectClass(env, activity);
  jobject imm = (*env)->CallObjectMethod(env, activity,
      (*env)->GetMethodID(env, act, "getSystemService", "(Ljava/lang/String;)Ljava/lang/Object;"), name);
  jobject window = (*env)->CallObjectMethod(env, activity,
      (*env)->GetMethodID(env, act, "getWindow", "()Landroid/view/Window;"));
  jclass win = (*env)->FindClass(env, "android/view/Window");
  jobject view = (*env)->CallObjectMethod(env, window,
      (*env)->GetMethodID(env, win, "getDecorView", "()Landroid/view/View;"));
  jclass immc = (*env)->FindClass(env, "android/view/inputmethod/InputMethodManager");
  if (check_exception() || !imm || !view) {
    LOG("could not reach InputMethodManager");
    return;
  }
  if (show) {
    (*env)->CallBooleanMethod(env, imm,
        (*env)->GetMethodID(env, immc, "showSoftInput", "(Landroid/view/View;I)Z"), view, 0);
  } else {
    jclass viewc = (*env)->FindClass(env, "android/view/View");
    jobject token = (*env)->CallObjectMethod(env, view,
        (*env)->GetMethodID(env, viewc, "getWindowToken", "()Landroid/os/IBinder;"));
    (*env)->CallBooleanMethod(env, imm,
        (*env)->GetMethodID(env, immc, "hideSoftInputFromWindow", "(Landroid/os/IBinder;I)Z"),
        token, 0);
    (*env)->DeleteLocalRef(env, viewc);
  }
  check_exception();
  (*env)->DeleteLocalRef(env, ctx);
  (*env)->DeleteLocalRef(env, act);
  (*env)->DeleteLocalRef(env, win);
  (*env)->DeleteLocalRef(env, immc);
}

/* --- window and frames ----------------------------------------------------- */

/* Pick the logical sizes and configure the window's buffers. The app draws
 * into the part of the window that is not covered by system bars or the
 * keyboard (the activity's content rect); the rest gets the app background. */
static void setup_window(void) {
  ANativeWindow *w = g.app->window;
  ANativeWindow_setBuffersGeometry(w, 0, 0, WINDOW_FORMAT_RGBA_8888); /* back to the surface size */
  int32_t pw = ANativeWindow_getWidth(w), ph = ANativeWindow_getHeight(w);
  if (pw <= 0 || ph <= 0) return;
  int32_t density = AConfiguration_getDensity(g.app->config);
  if (density <= 0 || density == ACONFIGURATION_DENSITY_ANY || density == ACONFIGURATION_DENSITY_NONE)
    density = ACONFIGURATION_DENSITY_MEDIUM;
  float scale = density / 160.0f;
  if (scale < 1) scale = 1;
  int32_t bw = (int32_t)(pw / scale + 0.5f), bh = (int32_t)(ph / scale + 0.5f);
  if (bw < 1) bw = 1;
  if (bh < 1) bh = 1;
  ANativeWindow_setBuffersGeometry(w, bw, bh, WINDOW_FORMAT_RGBA_8888);
  g.sx = (float)bw / pw;
  g.sy = (float)bh / ph;
  g.bw = bw;
  g.bh = bh;

  ARect r = g.app->contentRect;
  if (r.right <= r.left || r.bottom <= r.top) r = (ARect){0, 0, pw, ph};
  int32_t ox = (int32_t)(r.left * g.sx + 0.5f), oy = (int32_t)(r.top * g.sy + 0.5f);
  int32_t lw = (int32_t)(r.right * g.sx + 0.5f) - ox, lh = (int32_t)(r.bottom * g.sy + 0.5f) - oy;
  if (ox + lw > bw) lw = bw - ox;
  if (oy + lh > bh) lh = bh - oy;
  if (lw < 1) lw = 1;
  if (lh < 1) lh = 1;
  LOG("surface %dx%d px at %d dpi, buffer %dx%d, app %dx%d at (%d, %d)", pw, ph, density, bw, bh,
      lw, lh, ox, oy);
  if (!g.rt) {
    g.rt = uvl_android_make((uint32_t)lw, (uint32_t)lh);
  } else if (lw != g.lw || lh != g.lh) {
    push(EV_RESIZE, lw, lh, 0);
  }
  g.ox = ox;
  g.oy = oy;
  g.lw = lw;
  g.lh = lh;
  g.has_window = 1;
  g.rt = uvl_host_invalidate(g.rt); /* a new surface starts empty */
}

static uint32_t background_rgba(void) {
  lean_inc(g.rt);
  lean_object *bg = uvl_host_background(g.rt);
  const double *c = lean_float_array_cptr(bg);
  uint32_t px = 0;
  for (int i = 0; i < 4; i++) {
    double v = c[i] < 0 ? 0 : c[i] > 1 ? 1 : c[i];
    px |= (uint32_t)(v * 255 + 0.5) << (8 * i);
  }
  lean_dec_ref(bg);
  return px;
}

#ifdef UVL_ANDROID_GPU
/* --- GPU (wgpu-native on Vulkan) ------------------------------------------- */

int uvl_wgpu_init(const WGPUChainedStruct *surface_desc, const char *wgsl, const char *entries);
int uvl_wgpu_set_surface(const WGPUChainedStruct *surface_desc);
lean_object *uvl_gpu_adapter_name(lean_object *world);
lean_object *uvl_host_gpu_shader(lean_object *unit);
lean_object *uvl_host_gpu_entries(lean_object *unit);
lean_object *uvl_host_gpu_present(lean_object *rt, uint32_t x, uint32_t y, uint32_t w, uint32_t h);
lean_object *uvl_host_mark_clean(lean_object *rt);

static int gpu_state;              /* 0: not started, 1: drawing, -1: CPU */
static ANativeWindow *gpu_window;  /* the window the surface belongs to */

/* Start the GPU renderer on the current window, or move it to a new one. */
static int gpu_on(void) {
  if (gpu_state < 0) return 0;
  WGPUSurfaceSourceAndroidNativeWindow src = {
    .chain = {.sType = WGPUSType_SurfaceSourceAndroidNativeWindow}, .window = g.app->window};
  if (gpu_state == 0) {
    char prop[PROP_VALUE_MAX] = "";
    __system_property_get("debug.uvl.cpu", prop);
    if (prop[0] && prop[0] != '0') {
      gpu_state = -1;
      LOG("renderer: CPU (debug.uvl.cpu)");
      return 0;
    }
    prop[0] = 0;
    __system_property_get("debug.uvl.present", prop);
    if (prop[0]) setenv("UVL_PRESENT", prop, 1);
    lean_object *wgsl = uvl_host_gpu_shader(lean_box(0)), *entries = uvl_host_gpu_entries(lean_box(0));
    int ok = uvl_wgpu_init(&src.chain, lean_string_cstr(wgsl), lean_string_cstr(entries));
    lean_dec_ref(wgsl);
    lean_dec_ref(entries);
    gpu_state = ok ? 1 : -1;
    gpu_window = g.app->window;
    if (!ok) {
      LOG("renderer: CPU (the GPU renderer could not start)");
      return 0;
    }
    lean_object *name = uvl_gpu_adapter_name(lean_box(0));
    LOG("renderer: GPU on %s", lean_io_result_is_ok(name) ? lean_string_cstr(lean_io_result_get_value(name)) : "?");
    lean_dec_ref(name);
    return 1;
  }
  if (gpu_window != g.app->window) {
    gpu_window = g.app->window;
    if (!uvl_wgpu_set_surface(&src.chain)) {
      LOG("renderer: CPU (no GPU surface for the new window)");
      gpu_state = -1;
      return 0;
    }
  }
  return 1;
}

/* The window is going away: drop the surface (and its swapchain) first. */
static void gpu_off(void) {
  if (gpu_state > 0 && gpu_window) uvl_wgpu_set_surface(NULL);
  gpu_window = NULL;
}

static void present_gpu(void) {
  lean_inc(g.rt);
  lean_object *res = uvl_host_gpu_present(g.rt, g.ox, g.oy, g.bw, g.bh);
  if (!lean_io_result_is_ok(res)) lean_io_result_show_error(res);
  lean_dec_ref(res);
  g.rt = uvl_host_mark_clean(g.rt);
}
#endif

/* Rasterize the frame (only the damaged parts change) and copy it out. The
 * window's buffers rotate, so the whole frame is copied each time. */
static void present(void) {
#ifdef UVL_ANDROID_GPU
  if (gpu_on()) {
    present_gpu();
    return;
  }
#endif
  g.rt = uvl_host_present(g.rt);
  lean_inc(g.rt);
  lean_object *px = uvl_host_pixels(g.rt);
  lean_inc(g.rt);
  uint32_t w = uvl_host_width(g.rt);
  lean_inc(g.rt);
  uint32_t h = uvl_host_height(g.rt);
  uint32_t bg = background_rgba();
  ANativeWindow_Buffer buf;
  if (lean_sarray_size(px) >= (size_t)w * h * 4 && ANativeWindow_lock(g.app->window, &buf, NULL) == 0) {
    const uint8_t *src = lean_sarray_cptr(px);
    for (int32_t y = 0; y < buf.height; y++) {
      uint32_t *row = (uint32_t *)buf.bits + (size_t)y * buf.stride;
      int32_t sy = y - g.oy;
      int32_t x0 = g.ox, x1 = g.ox + (int32_t)w;
      if (x1 > buf.width) x1 = buf.width;
      if (sy < 0 || sy >= (int32_t)h || x0 >= x1) {
        for (int32_t x = 0; x < buf.width; x++) row[x] = bg;
        continue;
      }
      for (int32_t x = 0; x < x0; x++) row[x] = bg;
      memcpy(row + x0, src + (size_t)sy * w * 4, (size_t)(x1 - x0) * 4);
      for (int32_t x = x1; x < buf.width; x++) row[x] = bg;
    }
    ANativeWindow_unlockAndPost(g.app->window);
  }
  lean_dec_ref(px);
}

/* --- input ----------------------------------------------------------------- */

static int32_t on_input(struct android_app *app, AInputEvent *ev) {
  (void)app;
  if (!g.rt) return 0;
  if (AInputEvent_getType(ev) == AINPUT_EVENT_TYPE_MOTION) {
    int32_t raw = AMotionEvent_getAction(ev);
    int32_t action = raw & AMOTION_EVENT_ACTION_MASK;
    size_t idx = (size_t)((raw & AMOTION_EVENT_ACTION_POINTER_INDEX_MASK) >>
                          AMOTION_EVENT_ACTION_POINTER_INDEX_SHIFT);
    /* every finger, for multitouch gestures (Event.touchDown/Move/Up) */
    size_t n = AMotionEvent_getPointerCount(ev);
    for (size_t i = 0; i < n; i++) {
      int kind;
      if (action == AMOTION_EVENT_ACTION_MOVE) kind = EV_TOUCH_MOVE;
      else if (action == AMOTION_EVENT_ACTION_CANCEL) kind = EV_TOUCH_UP;
      else if (i != idx) continue;
      else if (action == AMOTION_EVENT_ACTION_DOWN || action == AMOTION_EVENT_ACTION_POINTER_DOWN)
        kind = EV_TOUCH_DOWN;
      else if (action == AMOTION_EVENT_ACTION_UP || action == AMOTION_EVENT_ACTION_POINTER_UP)
        kind = EV_TOUCH_UP;
      else continue;
      push(kind, AMotionEvent_getPointerId(ev, i), AMotionEvent_getX(ev, i) * g.sx - g.ox,
           AMotionEvent_getY(ev, i) * g.sy - g.oy);
    }
    /* only the first finger drives the pointer */
    double x = AMotionEvent_getX(ev, 0) * g.sx - g.ox, y = AMotionEvent_getY(ev, 0) * g.sy - g.oy;
    switch (action) {
    case AMOTION_EVENT_ACTION_DOWN:
      push(EV_MOVE, x, y, 0);
      push(EV_DOWN, x, y, 1);
      break;
    case AMOTION_EVENT_ACTION_MOVE:
      push(EV_MOVE, x, y, 0);
      break;
    case AMOTION_EVENT_ACTION_UP:
    case AMOTION_EVENT_ACTION_CANCEL:
      push(EV_UP, x, y, 1);
      push(EV_LEAVE, 0, 0, 0); /* no hover once the finger is lifted */
      break;
    default:
      break;
    }
    return 1;
  }
  if (AInputEvent_getType(ev) == AINPUT_EVENT_TYPE_KEY) {
    int32_t code = AKeyEvent_getKeyCode(ev);
    int32_t action = AKeyEvent_getAction(ev);
    if (action != AKEY_EVENT_ACTION_DOWN && action != AKEY_EVENT_ACTION_UP) return 0;
    int down = action == AKEY_EVENT_ACTION_DOWN;
    int kind = down ? EV_KEY_DOWN : EV_KEY_UP;
    if (code == AKEYCODE_BACK) {
      if (!g.keyboard) return 0; /* the system closes the app */
      if (!down) push(EV_KEY_DOWN, 0x1B, 0, 0); /* Escape: drop the focus */
      return 1;
    }
    uint32_t key = 0;
    switch (code) {
    case AKEYCODE_DEL: key = 0x08; break;
    case AKEYCODE_FORWARD_DEL: key = 0x7F; break;
    case AKEYCODE_ENTER: case AKEYCODE_NUMPAD_ENTER: key = 0x0D; break;
    case AKEYCODE_TAB: key = 0x09; break;
    case AKEYCODE_ESCAPE: key = 0x1B; break;
    case AKEYCODE_DPAD_LEFT: key = K_LEFT; break;
    case AKEYCODE_DPAD_RIGHT: key = K_RIGHT; break;
    case AKEYCODE_DPAD_UP: key = K_UP; break;
    case AKEYCODE_DPAD_DOWN: key = K_DOWN; break;
    case AKEYCODE_MOVE_HOME: key = K_HOME; break;
    case AKEYCODE_MOVE_END: key = K_END; break;
    case AKEYCODE_SHIFT_LEFT: case AKEYCODE_SHIFT_RIGHT: key = K_SHIFT; break;
    case AKEYCODE_CTRL_LEFT: case AKEYCODE_CTRL_RIGHT: key = K_CTRL; break;
    default: break;
    }
    if (key) {
      push(kind, key, 0, 0);
      return 1;
    }
    uint32_t ch = unicode_of(ev);
    if (!ch) return 0;
    if (AKeyEvent_getMetaState(ev) & AMETA_CTRL_ON) {
      push(kind, ch, 0, 0); /* shortcuts: Ctrl+A, Ctrl+C, ... */
    } else if (down) {
      push(EV_TEXT, ch, 0, 0);
    }
    return 1;
  }
  return 0;
}

/* --- lifecycle ------------------------------------------------------------- */

static void on_cmd(struct android_app *app, int32_t cmd) {
  (void)app;
  switch (cmd) {
  case APP_CMD_INIT_WINDOW:
    if (g.app->window) setup_window();
    break;
  case APP_CMD_WINDOW_RESIZED:
  case APP_CMD_CONFIG_CHANGED:
  case APP_CMD_CONTENT_RECT_CHANGED:
    if (g.app->window && g.has_window) setup_window();
    break;
  case APP_CMD_TERM_WINDOW:
    g.has_window = 0;
#ifdef UVL_ANDROID_GPU
    gpu_off();
#endif
    break;
  case APP_CMD_GAINED_FOCUS:
  case APP_CMD_RESUME:
    g.visible = 1;
    break;
  case APP_CMD_PAUSE:
    g.visible = 0;
    break;
  case APP_CMD_LOST_FOCUS:
    g.keyboard = -1; /* re-evaluate when the focus comes back */
    break;
  default:
    break;
  }
}

static int g_lean_ready = 0;

static int init_lean(void) {
  if (g_lean_ready) return 1;
  lean_initialize_runtime_module();
  lean_object *res = UVL_ANDROID_INIT(1);
  if (!lean_io_result_is_ok(res)) {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 0;
  }
  lean_dec_ref(res);
  lean_io_mark_end_initialization();
  g_lean_ready = 1;
  return 1;
}

/* The main loop. It runs on its own thread with a large stack (see
 * android_main), on a looper that replaces the glue's. */
static void *run(void *arg) {
  struct android_app *app = arg;
  ALooper *looper = ALooper_prepare(ALOOPER_PREPARE_ALLOW_NON_CALLBACKS);
  ALooper_addFd(looper, app->msgread, LOOPER_ID_MAIN, ALOOPER_EVENT_INPUT, NULL, &app->cmdPollSource);
  app->looper = looper; /* the glue attaches the input queue to app->looper */
  (*app->activity->vm)->AttachCurrentThread(app->activity->vm, &g.env, NULL);

  if (!init_lean()) {
    LOG("Lean initialization failed");
    ANativeActivity_finish(app->activity);
  }
  char prop[PROP_VALUE_MAX] = "";
  __system_property_get("debug.uvl.stats", prop);
  int stats = prop[0] && prop[0] != '0';
  double last = now_ms(), since = last, step_ms = 0, present_ms = 0;
  int frames = 0;
  while (!app->destroyRequested) {
    int animating = 0;
    if (g.rt) {
      lean_inc(g.rt);
      animating = uvl_host_animating(g.rt);
    }
    int active = g.has_window && g.visible;
    /* animating: wait what is left of a 16 ms frame since the last step (the
     * work of a frame counts towards it) */
    int timeout = -1;
    if (active && (animating || g.nevents)) {
      double left = last + 16 - now_ms();
      timeout = left <= 0 ? 0 : left >= 16 ? 16 : (int)left;
    }
    struct android_poll_source *src = NULL;
    int id;
    while ((id = ALooper_pollOnce(timeout, NULL, NULL, (void **)&src)) >= 0 || id == ALOOPER_POLL_CALLBACK) {
      if (src) src->process(app, src);
      src = NULL;
      if (app->destroyRequested) break;
      timeout = 0; /* drain what is pending, then step */
    }
    if (app->destroyRequested || !g.rt || !g_lean_ready) continue;

    double t = now_ms(), dt = t - last;
    last = t;
    lean_object *raw = lean_alloc_sarray(sizeof(double), 5 * g.nevents, 5 * g.nevents);
    memcpy(lean_float_array_cptr(raw), g.events, sizeof(double) * 5 * g.nevents);
    g.nevents = 0;
    g.rt = uvl_host_step(g.rt, raw, dt > 100 ? 100 : dt);
    double t1 = now_ms();
    step_ms += t1 - t;
    lean_inc(g.rt);
    if (uvl_host_quit(g.rt)) {
      ANativeActivity_finish(app->activity);
      continue;
    }
    lean_inc(g.rt);
    set_keyboard(uvl_host_text_focus(g.rt));
    if (!g.has_window) continue;
    lean_inc(g.rt);
    if (uvl_host_dirty(g.rt)) {
      present();
      frames++;
    }
    double t2 = now_ms();
    present_ms += t2 - t1;
    if (stats && t2 - since >= 2000) {
      if (frames)
        LOG("stats: %.1f fps | per frame: step %.2f ms, present %.2f ms", frames * 1000 / (t2 - since),
            step_ms / frames, present_ms / frames);
      since = t2;
      step_ms = present_ms = 0;
      frames = 0;
    }
  }
  set_keyboard(0);
  g.has_window = 0;
  (*app->activity->vm)->DetachCurrentThread(app->activity->vm);
  return NULL;
}

void android_main(struct android_app *app) {
  g.app = app;
  g.keyboard = 0;
  g.visible = 1;
  app->onAppCmd = on_cmd;
  app->onInputEvent = on_input;
  /* Lean code may recurse deeply; the glue's thread has the default 1 MB
   * stack, so the loop gets its own thread with a larger one. */
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, 64u << 20);
  pthread_t t;
  if (pthread_create(&t, &attr, run, app) != 0) {
    LOG("could not create the UVL thread");
    return;
  }
  pthread_join(t, NULL);
}
