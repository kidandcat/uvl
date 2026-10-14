// Browser shell for uvl apps compiled to WebAssembly.
//
// The Lean side (web_shell.c + UVL.AnyRuntime) is pure: it takes packed input
// events and returns RGBA frames. This file only
//   * collects DOM input into the packed format (5 doubles per event, same
//     encoding as the SDL shell, see UVL/App/Host.lean),
//   * runs the requestAnimationFrame loop, and
//   * presents frames with WebGPU (a textured full-screen triangle), falling
//     back to Canvas 2D when WebGPU is unavailable.

const EV = { move: 1, down: 2, up: 3, scroll: 4, keyDown: 5, keyUp: 6, text: 7, resize: 8, leave: 10 };

// DOM key names → SDL keycodes (printable keys use their codepoint).
const KEYS = {
  Enter: 0x0d, Escape: 0x1b, Backspace: 0x08, Tab: 0x09, Delete: 0x7f,
  ArrowRight: 0x4000004f, ArrowLeft: 0x40000050, ArrowDown: 0x40000051, ArrowUp: 0x40000052,
};

function keyCode(e) {
  if (e.key in KEYS) return KEYS[e.key];
  if ([...e.key].length === 1) return e.key.toLowerCase().codePointAt(0);
  return 0;
}

const SHADER = /* wgsl */ `
@group(0) @binding(0) var frame : texture_2d<f32>;

@vertex fn vs(@builtin(vertex_index) i : u32) -> @builtin(position) vec4f {
  let p = vec2f(f32((i << 1u) & 2u), f32(i & 2u));
  return vec4f(p * 2.0 - 1.0, 0.0, 1.0);
}

@fragment fn fs(@builtin(position) pos : vec4f) -> @location(0) vec4f {
  let c = textureLoad(frame, vec2i(pos.xy), 0);
  return vec4f(c.rgb, 1.0);
}`;

class WebGPUPresenter {
  static async create(canvas, onLost) {
    if (!navigator.gpu) return null;
    const adapter = await navigator.gpu.requestAdapter();
    if (!adapter) return null;
    const device = await adapter.requestDevice();
    device.addEventListener('uncapturederror', (e) => console.error(`WebGPU: ${e.error.message}`));
    device.lost.then((info) => onLost(info.message));
    const context = canvas.getContext('webgpu');
    if (!context) return null;
    return new WebGPUPresenter(canvas, device, context);
  }

  constructor(canvas, device, context) {
    this.name = 'webgpu';
    this.canvas = canvas;
    this.device = device;
    this.context = context;
    const format = navigator.gpu.getPreferredCanvasFormat();
    this.format = format;
    context.configure({
      device, format, alphaMode: 'opaque',
      usage: GPUTextureUsage.RENDER_ATTACHMENT | GPUTextureUsage.COPY_SRC,
    });
    const module = device.createShaderModule({ code: SHADER });
    this.pipeline = device.createRenderPipeline({
      layout: 'auto',
      vertex: { module, entryPoint: 'vs' },
      fragment: { module, entryPoint: 'fs', targets: [{ format }] },
      primitive: { topology: 'triangle-list' },
    });
    this.texture = null;
  }

  present(pixels, w, h, readback = null) {
    const { device } = this;
    if (!this.texture || this.texture.width !== w || this.texture.height !== h) {
      this.texture?.destroy();
      this.texture = device.createTexture({
        size: [w, h],
        format: 'rgba8unorm',
        usage: GPUTextureUsage.TEXTURE_BINDING | GPUTextureUsage.COPY_DST,
      });
      this.bindGroup = device.createBindGroup({
        layout: this.pipeline.getBindGroupLayout(0),
        entries: [{ binding: 0, resource: this.texture.createView() }],
      });
    }
    device.queue.writeTexture({ texture: this.texture }, pixels, { bytesPerRow: w * 4 }, [w, h]);
    const encoder = device.createCommandEncoder();
    const pass = encoder.beginRenderPass({
      colorAttachments: [{
        view: this.context.getCurrentTexture().createView(),
        loadOp: 'clear', storeOp: 'store', clearValue: [1, 1, 1, 1],
      }],
    });
    pass.setPipeline(this.pipeline);
    pass.setBindGroup(0, this.bindGroup);
    pass.draw(3);
    pass.end();
    if (readback) {
      // copy what was actually drawn, to verify the GPU path (tests)
      encoder.copyTextureToBuffer({ texture: this.context.getCurrentTexture() },
        { buffer: readback.buffer, bytesPerRow: readback.stride }, [w, h]);
    }
    device.queue.submit([encoder.finish()]);
  }

  /** Present `pixels` and read back the canvas texture as RGBA bytes. */
  async readback(pixels, w, h) {
    const stride = Math.ceil(w * 4 / 256) * 256;
    const buffer = this.device.createBuffer({
      size: stride * h, usage: GPUBufferUsage.COPY_DST | GPUBufferUsage.MAP_READ,
    });
    this.present(pixels, w, h, { buffer, stride });
    await buffer.mapAsync(GPUMapMode.READ);
    const src = new Uint8Array(buffer.getMappedRange());
    const out = new Uint8Array(w * h * 4);
    const bgra = this.format === 'bgra8unorm';
    for (let y = 0; y < h; y++) {
      for (let x = 0; x < w; x++) {
        const i = y * stride + x * 4, o = (y * w + x) * 4;
        out[o] = src[i + (bgra ? 2 : 0)];
        out[o + 1] = src[i + 1];
        out[o + 2] = src[i + (bgra ? 0 : 2)];
        out[o + 3] = src[i + 3];
      }
    }
    buffer.unmap();
    buffer.destroy();
    return out;
  }
}

class Canvas2DPresenter {
  constructor(canvas) {
    this.name = 'canvas2d';
    this.ctx = canvas.getContext('2d');
  }

  present(pixels, w, h) {
    this.ctx.putImageData(new ImageData(new Uint8ClampedArray(pixels), w, h), 0, 0);
  }
}

/** Start a uvl app on `canvas`. Resolves to a small control object.
 * `backend: 'canvas2d'` skips WebGPU. */
export async function startUVL(canvas, createModule, { backend } = {}) {
  const size = () => {
    const r = canvas.getBoundingClientRect();
    return [Math.max(1, Math.round(r.width)), Math.max(1, Math.round(r.height))];
  };
  let [w, h] = size();
  canvas.width = w;
  canvas.height = h;

  const mod = await createModule();
  const framePixels = () => mod.HEAPU8.subarray(mod._uvl_frame_ptr(), mod._uvl_frame_ptr() + w * h * 4);
  const state = { backend: 'none', frames: 0, quit: false };

  // A lost WebGPU device (driver reset, or software adapters in some headless
  // browsers) falls back to Canvas 2D. A canvas that has a WebGPU context can
  // never get a 2D one, so it is swapped for a fresh element.
  let presenter = null;
  const fallBack = (why) => {
    if (presenter?.name !== 'webgpu') return;
    console.warn(`WebGPU device lost (${why}); falling back to Canvas 2D`);
    const fresh = canvas.cloneNode(false);
    canvas.replaceWith(fresh);
    canvas = fresh;
    canvas.width = w;
    canvas.height = h;
    bind(canvas);
    presenter = new Canvas2DPresenter(canvas);
    state.backend = presenter.name;
    if (state.frames) presenter.present(framePixels(), w, h);
  };
  if (backend !== 'canvas2d') {
    presenter = await WebGPUPresenter.create(canvas, (why) => fallBack(why)).catch((e) => {
      console.warn(`WebGPU unavailable: ${e.message}`);
      return null;
    });
  }
  presenter ??= new Canvas2DPresenter(canvas);
  state.backend = presenter.name;
  if (!mod._uvl_init(w, h)) throw new Error('uvl: Lean initialization failed');

  const queue = [];
  const push = (kind, a = 0, b = 0, c = 0, d = 0) => queue.push(kind, a, b, c, d);
  const button = (e) => [1, 2, 3][e.button] ?? e.button + 1;
  const resizer = new ResizeObserver(() => {
    const [nw, nh] = size();
    if (nw !== w || nh !== h) push(EV.resize, nw, nh);
  });

  function bind(el) {
    el.addEventListener('pointermove', (e) => push(EV.move, e.offsetX, e.offsetY));
    el.addEventListener('pointerdown', (e) => {
      el.setPointerCapture(e.pointerId);
      el.focus();
      push(EV.down, e.offsetX, e.offsetY, button(e));
    });
    el.addEventListener('pointerup', (e) => push(EV.up, e.offsetX, e.offsetY, button(e)));
    el.addEventListener('pointerleave', () => push(EV.leave));
    el.addEventListener('wheel', (e) => { e.preventDefault(); push(EV.scroll, e.deltaX, e.deltaY); }, { passive: false });
    el.addEventListener('contextmenu', (e) => e.preventDefault());
    el.addEventListener('keydown', (e) => {
      const code = keyCode(e);
      if (code) push(EV.keyDown, code);
      if ([...e.key].length === 1 && !e.ctrlKey && !e.metaKey) push(EV.text, e.key.codePointAt(0));
      if (e.key === 'Tab' || e.key.startsWith('Arrow') || e.key === ' ') e.preventDefault();
    });
    el.addEventListener('keyup', (e) => { const code = keyCode(e); if (code) push(EV.keyUp, code); });
    resizer.disconnect();
    resizer.observe(el);
  }
  bind(canvas);

  let buf = 0, cap = 0, last = performance.now();

  function frame(now) {
    const n = queue.length / 5;
    if (n > cap) {
      if (buf) mod._free(buf);
      cap = Math.max(n, 64);
      buf = mod._malloc(cap * 40);
    }
    if (n) mod.HEAPF64.set(queue, buf / 8);
    queue.length = 0;
    const r = mod._uvl_step(buf, n, now - last);
    last = now;
    if (r === 2) { state.quit = true; return; }
    if (r === 1) {
      w = mod._uvl_width();
      h = mod._uvl_height();
      if (canvas.width !== w || canvas.height !== h) { canvas.width = w; canvas.height = h; }
      presenter.present(framePixels(), w, h);
      state.frames++;
    }
    requestAnimationFrame(frame);
  }
  requestAnimationFrame(frame);

  return {
    state,
    /** The canvas currently showing the app (replaced on WebGPU fallback). */
    get canvas() { return canvas; },
    /** Centre of tap target `i` in canvas pixels, or null. */
    targetCenter(i) {
      const p = mod._uvl_target_center(i);
      return p ? [mod.HEAPF64[p / 8], mod.HEAPF64[p / 8 + 1]] : null;
    },
    /** Copy of the last presented frame (RGBA). */
    snapshot() {
      const p = mod._uvl_frame_ptr();
      return p ? mod.HEAPU8.slice(p, p + w * h * 4) : null;
    },
    /** What the GPU actually drew for the last frame (WebGPU only, for tests). */
    async gpuReadback() {
      if (!mod._uvl_frame_ptr() || !presenter.readback) return null;
      return presenter.readback(mod.HEAPU8.slice(mod._uvl_frame_ptr(), mod._uvl_frame_ptr() + w * h * 4), w, h);
    },
  };
}
