/*
 * Desktop GPU renderer for uvl, on wgpu-native (webgpu.h).
 *
 * The same thing the browser's GPURenderer does (web/uvl-web.js): compile the
 * WGSL that Lean generates (UVL/GPU/Kernels.lean), upload the primitives Lean
 * lowered the scene to (UVL/GPU/Batch.lean) and draw them, one pipeline per
 * primitive kind. No rendering logic lives here.
 *
 * It renders either to a window surface (created by the SDL shell from the
 * window's native handles, see uvl_sdl_gpu_init in sdl_shell.c, or by the
 * Android shell from its ANativeWindow) or, headless, to an offscreen texture
 * that can be read back (tests).
 */
#include <lean/lean.h>
#include <webgpu/webgpu.h>
#include <webgpu/wgpu.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define PRIM_STRIDE 36 /* floats per primitive (UVL/GPU/Kernels.lean) */
#define MAX_KINDS 16

static WGPUInstance instance;
static WGPUAdapter adapter;
static WGPUDevice device;
static WGPUQueue queue;
static WGPUSurface surface;
static WGPUTextureFormat format = WGPUTextureFormat_RGBA8Unorm;
static WGPUPresentMode present_mode = WGPUPresentMode_Fifo;
static WGPUBindGroupLayout bgl;
static WGPURenderPipeline pipelines[MAX_KINDS];
static int nkinds;
static WGPUBuffer prims_buf, data_buf, screen_buf, atlas_buf, tex_buf;
static uint64_t prims_cap, data_cap, atlas_cap, tex_cap;
static WGPUBindGroup bind_group;
static uint32_t surf_w, surf_h;
static float *scratch;
static size_t scratch_cap;
static char last_error[512];

static WGPUStringView sv(const char *s) { return (WGPUStringView){s, WGPU_STRLEN}; }

static void on_error(WGPUDevice const *d, WGPUErrorType type, WGPUStringView msg, void *u1, void *u2) {
  (void)d; (void)u1; (void)u2;
  snprintf(last_error, sizeof last_error, "WebGPU error %d: %.*s", (int)type, (int)msg.length, msg.data);
  fprintf(stderr, "%s\n", last_error);
}

static void on_adapter(WGPURequestAdapterStatus st, WGPUAdapter a, WGPUStringView msg, void *u1, void *u2) {
  *(int *)u2 = 1;
  if (st == WGPURequestAdapterStatus_Success) *(WGPUAdapter *)u1 = a;
  else fprintf(stderr, "uvl: no GPU adapter: %.*s\n", (int)msg.length, msg.data);
}

static void on_device(WGPURequestDeviceStatus st, WGPUDevice d, WGPUStringView msg, void *u1, void *u2) {
  *(int *)u2 = 1;
  if (st == WGPURequestDeviceStatus_Success) *(WGPUDevice *)u1 = d;
  else fprintf(stderr, "uvl: no GPU device: %.*s\n", (int)msg.length, msg.data);
}

/* Split a comma-separated list in place. */
static int split(char *s, char **out, int max) {
  int n = 0;
  while (*s && n < max) {
    out[n++] = s;
    char *c = strchr(s, ',');
    if (!c) break;
    *c = 0;
    s = c + 1;
  }
  return n;
}

static int create_pipelines(const char *wgsl, const char *entries) {
  WGPUShaderSourceWGSL src = {.chain = {.sType = WGPUSType_ShaderSourceWGSL}, .code = sv(wgsl)};
  WGPUShaderModuleDescriptor smd = {.nextInChain = &src.chain};
  WGPUShaderModule module = wgpuDeviceCreateShaderModule(device, &smd);
  if (!module) return 0;

  WGPUShaderStage vis = WGPUShaderStage_Vertex | WGPUShaderStage_Fragment;
  WGPUBindGroupLayoutEntry e[5] = {
    {.binding = 0, .visibility = vis, .buffer = {.type = WGPUBufferBindingType_ReadOnlyStorage}},
    {.binding = 1, .visibility = vis, .buffer = {.type = WGPUBufferBindingType_ReadOnlyStorage}},
    {.binding = 2, .visibility = vis, .buffer = {.type = WGPUBufferBindingType_Uniform}},
    {.binding = 3, .visibility = vis, .buffer = {.type = WGPUBufferBindingType_ReadOnlyStorage}},
    {.binding = 4, .visibility = vis, .buffer = {.type = WGPUBufferBindingType_ReadOnlyStorage}},
  };
  WGPUBindGroupLayoutDescriptor bgld = {.entryCount = 5, .entries = e};
  bgl = wgpuDeviceCreateBindGroupLayout(device, &bgld);
  WGPUPipelineLayoutDescriptor pld = {.bindGroupLayoutCount = 1, .bindGroupLayouts = &bgl};
  WGPUPipelineLayout layout = wgpuDeviceCreatePipelineLayout(device, &pld);

  /* straight alpha over the frame, like FrameBuffer.blend */
  WGPUBlendState blend = {
    .color = {.operation = WGPUBlendOperation_Add, .srcFactor = WGPUBlendFactor_SrcAlpha,
              .dstFactor = WGPUBlendFactor_OneMinusSrcAlpha},
    .alpha = {.operation = WGPUBlendOperation_Add, .srcFactor = WGPUBlendFactor_One,
              .dstFactor = WGPUBlendFactor_OneMinusSrcAlpha},
  };
  WGPUColorTargetState target = {.format = format, .blend = &blend, .writeMask = WGPUColorWriteMask_All};
  char *names = strdup(entries), *list[MAX_KINDS];
  nkinds = split(names, list, MAX_KINDS);
  last_error[0] = 0;
  for (int k = 0; k < nkinds; k++) {
    WGPUFragmentState fs = {.module = module, .entryPoint = sv(list[k]), .targetCount = 1, .targets = &target};
    WGPURenderPipelineDescriptor rpd = {
      .layout = layout,
      .vertex = {.module = module, .entryPoint = sv("vs")},
      .primitive = {.topology = WGPUPrimitiveTopology_TriangleList},
      .multisample = {.count = 1, .mask = ~0u},
      .fragment = &fs,
    };
    pipelines[k] = wgpuDeviceCreateRenderPipeline(device, &rpd);
  }
  free(names);
  wgpuShaderModuleRelease(module);
  wgpuPipelineLayoutRelease(layout);
  wgpuDevicePoll(device, 1, NULL);
  return last_error[0] == 0;
}

static int init_device(void) {
  int done = 0;
  WGPURequestAdapterOptions ao = {.compatibleSurface = surface,
                                  .powerPreference = WGPUPowerPreference_HighPerformance};
  wgpuInstanceRequestAdapter(instance, &ao,
    (WGPURequestAdapterCallbackInfo){.mode = WGPUCallbackMode_AllowProcessEvents,
                                     .callback = on_adapter, .userdata1 = &adapter, .userdata2 = &done});
  while (!done) wgpuInstanceProcessEvents(instance);
  if (!adapter) return 0;
  done = 0;
  WGPUDeviceDescriptor dd = {
    .uncapturedErrorCallbackInfo = {.callback = on_error},
  };
  wgpuAdapterRequestDevice(adapter, &dd,
    (WGPURequestDeviceCallbackInfo){.mode = WGPUCallbackMode_AllowProcessEvents,
                                    .callback = on_device, .userdata1 = &device, .userdata2 = &done});
  while (!done) wgpuInstanceProcessEvents(instance);
  if (!device) return 0;
  queue = wgpuDeviceGetQueue(device);
  WGPUBufferDescriptor bd = {.size = 16, .usage = WGPUBufferUsage_Uniform | WGPUBufferUsage_CopyDst};
  screen_buf = wgpuDeviceCreateBuffer(device, &bd);
  WGPUBufferDescriptor ad = {.size = 16, .usage = WGPUBufferUsage_Storage | WGPUBufferUsage_CopyDst};
  atlas_buf = wgpuDeviceCreateBuffer(device, &ad);
  atlas_cap = 16;
  tex_buf = wgpuDeviceCreateBuffer(device, &ad);
  tex_cap = 16;
  return 1;
}

/* Set up instance, adapter, device and pipelines. `surface_desc` chains the
 * native window handles, or is NULL for headless rendering. */
int uvl_wgpu_init(const WGPUChainedStruct *surface_desc, const char *wgsl, const char *entries) {
  instance = wgpuCreateInstance(NULL);
  if (!instance) return 0;
  if (surface_desc) {
    WGPUSurfaceDescriptor sd = {.nextInChain = surface_desc};
    surface = wgpuInstanceCreateSurface(instance, &sd);
    if (!surface) return 0;
  }
  if (!init_device()) return 0;
  if (surface) {
    WGPUSurfaceCapabilities caps = {0};
    wgpuSurfaceGetCapabilities(surface, adapter, &caps);
    if (caps.formatCount == 0) return 0;
    format = caps.formats[0];
    for (size_t i = 0; i < caps.formatCount; i++) /* prefer non-sRGB, as on the web */
      if (caps.formats[i] == WGPUTextureFormat_BGRA8Unorm || caps.formats[i] == WGPUTextureFormat_RGBA8Unorm) {
        format = caps.formats[i];
        break;
      }
    /* UVL_PRESENT=immediate or mailbox: do not wait for vsync (measuring) */
    const char *want = getenv("UVL_PRESENT");
    WGPUPresentMode mode = !want ? WGPUPresentMode_Fifo
      : !strcmp(want, "immediate") ? WGPUPresentMode_Immediate
      : !strcmp(want, "mailbox") ? WGPUPresentMode_Mailbox : WGPUPresentMode_Fifo;
    for (size_t i = 0; i < caps.presentModeCount; i++)
      if (caps.presentModes[i] == mode) present_mode = mode;
    if (want && present_mode != mode) fprintf(stderr, "uvl: present mode %s unsupported\n", want);
    wgpuSurfaceCapabilitiesFreeMembers(caps);
  }
  return create_pipelines(wgsl, entries);
}

static void configure(uint32_t w, uint32_t h) {
  if (!surface || (w == surf_w && h == surf_h)) return;
  WGPUSurfaceConfiguration c = {
    .device = device, .format = format, .usage = WGPUTextureUsage_RenderAttachment,
    .width = w, .height = h, .alphaMode = WGPUCompositeAlphaMode_Auto,
    .presentMode = present_mode,
  };
  wgpuSurfaceConfigure(surface, &c);
  surf_w = w;
  surf_h = h;
}

/* A storage buffer of at least `bytes`; rebuilds the bind group when it grows.
 * Returns 1 when the buffer is new (its contents must be written in full). */
static int ensure(WGPUBuffer *buf, uint64_t *cap, uint64_t bytes) {
  bytes = bytes < 16 ? 16 : (bytes + 15) / 16 * 16;
  if (*buf && *cap >= bytes) return 0;
  if (*buf) wgpuBufferRelease(*buf);
  if (bytes < *cap * 2) bytes = *cap * 2;
  WGPUBufferDescriptor bd = {.size = bytes, .usage = WGPUBufferUsage_Storage | WGPUBufferUsage_CopyDst};
  *buf = wgpuDeviceCreateBuffer(device, &bd);
  *cap = bytes;
  if (bind_group) wgpuBindGroupRelease(bind_group);
  bind_group = NULL;
  return 1;
}

/* Bytes written to the primitive and data buffers by the last draw, and
 * whether the next draw must write them in full (a frame was dropped). */
static uint64_t uploaded;
static int force_full;

/* Replace the window surface (Android destroys and recreates its window when
 * the app goes to the background), or drop it with NULL. The device and the
 * pipelines stay; the next frame is uploaded in full. */
int uvl_wgpu_set_surface(const WGPUChainedStruct *surface_desc) {
  if (surface) {
    if (surf_w) wgpuSurfaceUnconfigure(surface);
    wgpuSurfaceRelease(surface);
    surface = NULL;
  }
  surf_w = surf_h = 0;
  force_full = 1;
  if (!surface_desc) return 1;
  WGPUSurfaceDescriptor sd = {.nextInChain = surface_desc};
  surface = wgpuInstanceCreateSurface(instance, &sd);
  return surface != NULL;
}

/* Write `arr` (as f32) to `buf`: only the float ranges `ranges` (flattened
 * start/stop pairs, see `Batch.changedRanges`) unless `full`. */
static void upload(WGPUBuffer buf, b_lean_obj_arg arr, b_lean_obj_arg ranges, int full) {
  size_t n = lean_sarray_size(arr);
  if (!n) return;
  if (n > scratch_cap) {
    free(scratch);
    scratch_cap = n + n / 2;
    scratch = malloc(sizeof(float) * scratch_cap);
  }
  const double *src = lean_float_array_cptr(arr);
  const double *r = lean_float_array_cptr(ranges);
  size_t nr = full ? 1 : lean_sarray_size(ranges) / 2;
  for (size_t k = 0; k < nr; k++) {
    size_t s = full ? 0 : (size_t)r[2 * k], e = full ? n : (size_t)r[2 * k + 1];
    if (e > n) e = n;
    if (e <= s) continue;
    for (size_t i = s; i < e; i++) scratch[i] = (float)src[i];
    wgpuQueueWriteBuffer(queue, buf, sizeof(float) * s, scratch + s, sizeof(float) * (e - s));
    uploaded += sizeof(float) * (e - s);
  }
}

static void on_mapped(WGPUMapAsyncStatus st, WGPUStringView msg, void *u1, void *u2) {
  (void)msg; (void)u2;
  *(int *)u1 = st == WGPUMapAsyncStatus_Success ? 1 : -1;
}

/* Draw the primitives onto `target`, then optionally copy it into `readback`. */
static void draw(WGPUTexture target, b_lean_obj_arg prims, b_lean_obj_arg ranges, int full,
                 uint32_t count, uint32_t w, uint32_t h,
                 b_lean_obj_arg bg, WGPUBuffer readback, uint32_t stride) {
  full |= ensure(&prims_buf, &prims_cap, sizeof(float) * lean_sarray_size(prims));
  if (!bind_group) {
    WGPUBindGroupEntry e[5] = {
      {.binding = 0, .buffer = prims_buf, .size = prims_cap},
      {.binding = 1, .buffer = data_buf, .size = data_cap},
      {.binding = 2, .buffer = screen_buf, .size = 16},
      {.binding = 3, .buffer = atlas_buf, .size = atlas_cap},
      {.binding = 4, .buffer = tex_buf, .size = tex_cap},
    };
    WGPUBindGroupDescriptor bgd = {.layout = bgl, .entryCount = 5, .entries = e};
    bind_group = wgpuDeviceCreateBindGroup(device, &bgd);
  }
  upload(prims_buf, prims, ranges, full);
  float screen[4] = {(float)w, (float)h, 0, 0};
  wgpuQueueWriteBuffer(queue, screen_buf, 0, screen, sizeof screen);

  const double *c = lean_float_array_cptr(bg);
  WGPUTextureView view = wgpuTextureCreateView(target, NULL);
  WGPURenderPassColorAttachment ca = {
    .view = view, .depthSlice = WGPU_DEPTH_SLICE_UNDEFINED,
    .loadOp = WGPULoadOp_Clear, .storeOp = WGPUStoreOp_Store,
    .clearValue = {c[0], c[1], c[2], 1.0},
  };
  WGPUCommandEncoder enc = wgpuDeviceCreateCommandEncoder(device, NULL);
  WGPURenderPassDescriptor rpd = {.colorAttachmentCount = 1, .colorAttachments = &ca};
  WGPURenderPassEncoder pass = wgpuCommandEncoderBeginRenderPass(enc, &rpd);
  wgpuRenderPassEncoderSetBindGroup(pass, 0, bind_group, 0, NULL);
  /* consecutive primitives of the same kind share a draw call (paint order is kept) */
  const double *p = lean_float_array_cptr(prims);
  for (uint32_t i = 0; i < count;) {
    int kind = (int)p[(size_t)i * PRIM_STRIDE];
    uint32_t j = i + 1;
    while (j < count && (int)p[(size_t)j * PRIM_STRIDE] == kind) j++;
    if (kind >= 0 && kind < nkinds) {
      wgpuRenderPassEncoderSetPipeline(pass, pipelines[kind]);
      wgpuRenderPassEncoderDraw(pass, 6, j - i, 0, i);
    }
    i = j;
  }
  wgpuRenderPassEncoderEnd(pass);
  wgpuRenderPassEncoderRelease(pass);
  if (readback) {
    WGPUTexelCopyTextureInfo src = {.texture = target};
    WGPUTexelCopyBufferInfo dst = {.buffer = readback, .layout = {.bytesPerRow = stride, .rowsPerImage = h}};
    WGPUExtent3D size = {w, h, 1};
    wgpuCommandEncoderCopyTextureToBuffer(enc, &src, &dst, &size);
  }
  WGPUCommandBuffer cmd = wgpuCommandEncoderFinish(enc, NULL);
  wgpuQueueSubmit(queue, 1, &cmd);
  wgpuCommandBufferRelease(cmd);
  wgpuCommandEncoderRelease(enc);
  wgpuTextureViewRelease(view);
}

static lean_obj_res io_error(const char *what) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(what)));
}

/* Lean: `GPU.drawRaw prims data primRanges dataRanges full count w h bg readback :
 * IO ByteArray`. Draws a frame to the window surface (presenting it), or
 * offscreen when headless. Only the given ranges of the arrays are written to
 * the GPU, unless `full`. With `readback` (or headless), returns the frame as
 * tightly packed RGBA. */
LEAN_EXPORT lean_obj_res uvl_gpu_draw(b_lean_obj_arg prims, b_lean_obj_arg data,
                                      b_lean_obj_arg prim_ranges, b_lean_obj_arg data_ranges,
                                      uint8_t full, uint32_t count,
                                      uint32_t w, uint32_t h, b_lean_obj_arg bg, uint8_t want,
                                      lean_obj_arg world) {
  (void)world;
  if (!device) return io_error("uvl: GPU not initialized");
  if (w == 0 || h == 0) return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
  uploaded = 0;
  full |= force_full;
  force_full = 0;
  int full_data = full | ensure(&data_buf, &data_cap, sizeof(float) * lean_sarray_size(data));
  upload(data_buf, data, data_ranges, full_data);

  WGPUTexture target = NULL, offscreen = NULL;
  if (surface && !want) {
    configure(w, h);
    WGPUSurfaceTexture st;
    wgpuSurfaceGetCurrentTexture(surface, &st);
    if (st.status != WGPUSurfaceGetCurrentTextureStatus_SuccessOptimal &&
        st.status != WGPUSurfaceGetCurrentTextureStatus_SuccessSuboptimal) {
      surf_w = surf_h = 0; /* reconfigure next time */
      force_full = 1;      /* the primitives of this frame were not written */
      return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
    }
    draw(st.texture, prims, prim_ranges, full, count, w, h, bg, NULL, 0);
    wgpuSurfacePresent(surface);
    wgpuTextureRelease(st.texture);
    return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
  }

  /* offscreen: render into a texture of the pipelines' format and read it back */
  WGPUTextureDescriptor td = {
    .usage = WGPUTextureUsage_RenderAttachment | WGPUTextureUsage_CopySrc,
    .dimension = WGPUTextureDimension_2D, .size = {w, h, 1}, .format = format,
    .mipLevelCount = 1, .sampleCount = 1,
  };
  offscreen = wgpuDeviceCreateTexture(device, &td);
  target = offscreen;
  uint32_t stride = (w * 4 + 255) / 256 * 256;
  WGPUBufferDescriptor bd = {.size = (uint64_t)stride * h,
                             .usage = WGPUBufferUsage_CopyDst | WGPUBufferUsage_MapRead};
  WGPUBuffer rb = wgpuDeviceCreateBuffer(device, &bd);
  draw(target, prims, prim_ranges, full, count, w, h, bg, rb, stride);
  int done = 0;
  wgpuBufferMapAsync(rb, WGPUMapMode_Read, 0, bd.size,
    (WGPUBufferMapCallbackInfo){.mode = WGPUCallbackMode_AllowProcessEvents,
                                .callback = on_mapped, .userdata1 = &done});
  while (!done) {
    wgpuDevicePoll(device, 1, NULL);
    wgpuInstanceProcessEvents(instance);
  }
  lean_object *out = lean_alloc_sarray(1, (size_t)w * h * 4, (size_t)w * h * 4);
  if (done > 0) {
    const uint8_t *src = wgpuBufferGetConstMappedRange(rb, 0, bd.size);
    uint8_t *o = lean_sarray_cptr(out);
    int bgra = format == WGPUTextureFormat_BGRA8Unorm || format == WGPUTextureFormat_BGRA8UnormSrgb;
    for (uint32_t y = 0; y < h; y++)
      for (uint32_t x = 0; x < w; x++) {
        const uint8_t *s = src + (size_t)y * stride + x * 4;
        uint8_t *d = o + ((size_t)y * w + x) * 4;
        d[0] = s[bgra ? 2 : 0]; d[1] = s[1]; d[2] = s[bgra ? 0 : 2]; d[3] = s[3];
      }
    wgpuBufferUnmap(rb);
  }
  wgpuBufferRelease(rb);
  wgpuTextureRelease(offscreen);
  return lean_io_result_mk_ok(out);
}

/* Lean: `GPU.uploadedBytes : IO UInt64`, bytes written by the last draw. */
LEAN_EXPORT lean_obj_res uvl_gpu_uploaded_bytes(lean_obj_arg world) {
  (void)world;
  return lean_io_result_mk_ok(lean_box_uint64(uploaded));
}

/* Lean: `GPU.atlasReset floats : IO Unit`. Replace the MSDF atlas buffer by a
 * zeroed one of `floats` floats (a frame drawing from a different atlas). */
LEAN_EXPORT lean_obj_res uvl_gpu_atlas_reset(uint32_t floats, lean_obj_arg world) {
  (void)world;
  if (!device) return io_error("uvl: GPU not initialized");
  uint64_t bytes = floats < 4 ? 16 : ((uint64_t)floats * 4 + 15) / 16 * 16;
  if (atlas_buf) wgpuBufferRelease(atlas_buf);
  WGPUBufferDescriptor bd = {.size = bytes, .usage = WGPUBufferUsage_Storage | WGPUBufferUsage_CopyDst};
  atlas_buf = wgpuDeviceCreateBuffer(device, &bd);
  atlas_cap = bytes;
  if (bind_group) wgpuBindGroupRelease(bind_group);
  bind_group = NULL;
  return lean_io_result_mk_ok(lean_box(0));
}

/* Lean: `GPU.atlasWrite offset texels : IO Unit`. Upload one glyph cell at
 * float offset `offset` of the atlas buffer. */
LEAN_EXPORT lean_obj_res uvl_gpu_atlas_write(uint32_t offset, b_lean_obj_arg texels, lean_obj_arg world) {
  (void)world;
  if (!device) return io_error("uvl: GPU not initialized");
  size_t n = lean_sarray_size(texels);
  if (n && ((uint64_t)offset + n) * 4 <= atlas_cap) {
    float *tmp = malloc(sizeof(float) * n);
    const double *src = lean_float_array_cptr(texels);
    for (size_t i = 0; i < n; i++) tmp[i] = (float)src[i];
    wgpuQueueWriteBuffer(queue, atlas_buf, (uint64_t)offset * 4, tmp, sizeof(float) * n);
    free(tmp);
  }
  return lean_io_result_mk_ok(lean_box(0));
}

/* Lean: `GPU.textureUpload pixels : IO Unit`. Replace the sprite texture
 * buffer by the texture's RGBA bytes (read by the shader as packed u32s). */
LEAN_EXPORT lean_obj_res uvl_gpu_texture_upload(b_lean_obj_arg pixels, lean_obj_arg world) {
  (void)world;
  if (!device) return io_error("uvl: GPU not initialized");
  size_t n = lean_sarray_size(pixels);
  uint64_t bytes = n < 16 ? 16 : ((uint64_t)n + 15) / 16 * 16;
  if (tex_buf) wgpuBufferRelease(tex_buf);
  WGPUBufferDescriptor bd = {.size = bytes, .usage = WGPUBufferUsage_Storage | WGPUBufferUsage_CopyDst};
  tex_buf = wgpuDeviceCreateBuffer(device, &bd);
  tex_cap = bytes;
  if (n / 4 * 4 > 0) wgpuQueueWriteBuffer(queue, tex_buf, 0, lean_sarray_cptr(pixels), n / 4 * 4);
  if (bind_group) wgpuBindGroupRelease(bind_group);
  bind_group = NULL;
  return lean_io_result_mk_ok(lean_box(0));
}

/* Lean: `GPU.initHeadless wgsl entries : IO Bool` (no window, offscreen only). */
LEAN_EXPORT lean_obj_res uvl_gpu_init_headless(b_lean_obj_arg wgsl, b_lean_obj_arg entries,
                                               lean_obj_arg world) {
  (void)world;
  int ok = uvl_wgpu_init(NULL, lean_string_cstr(wgsl), lean_string_cstr(entries));
  return lean_io_result_mk_ok(lean_box(ok ? 1 : 0));
}

/* Lean: `GPU.adapterName : IO String`. */
LEAN_EXPORT lean_obj_res uvl_gpu_adapter_name(lean_obj_arg world) {
  (void)world;
  if (!adapter) return lean_io_result_mk_ok(lean_mk_string(""));
  WGPUAdapterInfo info = {0};
  wgpuAdapterGetInfo(adapter, &info);
  char buf[256];
  snprintf(buf, sizeof buf, "%.*s (%.*s)", (int)info.device.length, info.device.data,
           (int)info.description.length, info.description.data);
  wgpuAdapterInfoFreeMembers(info);
  return lean_io_result_mk_ok(lean_mk_string(buf));
}
