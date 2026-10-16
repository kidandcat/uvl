// Browser shell for uvl apps compiled to WebAssembly.
//
// The Lean side (web_shell.c + UVL.AnyRuntime) is pure: it takes packed input
// events and returns frames. This file only
//   * collects DOM input into the packed format (5 doubles per event, same
//     encoding as the SDL shell, see UVL/App/Host.lean),
//   * runs the requestAnimationFrame loop, and
//   * draws frames with one of three backends:
//       gpu      the scene rendered on the GPU: Lean lowers it to primitives
//                and generates the WGSL program (UVL/GPU); this file only
//                uploads buffers and issues one draw call (default);
//       webgpu   Lean rasterizes on the CPU, the GPU only presents the
//                damaged windows of the frame;
//       canvas2d the same CPU frames through putImageData (no WebGPU).

const EV = { move: 1, down: 2, up: 3, scroll: 4, keyDown: 5, keyUp: 6, text: 7, resize: 8, leave: 10,
  compose: 11, composeEnd: 12 };

// DOM key names → SDL keycodes (printable keys use their codepoint).
const KEYS = {
  Enter: 0x0d, Escape: 0x1b, Backspace: 0x08, Tab: 0x09, Delete: 0x7f,
  ArrowRight: 0x4000004f, ArrowLeft: 0x40000050, ArrowDown: 0x40000051, ArrowUp: 0x40000052,
  Home: 0x4000004a, End: 0x4000004d,
  Shift: 0x400000e1, Control: 0x400000e0, Meta: 0x400000e0,
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


// Pixels outside every primitive keep the clear color; each primitive blends
// `shade(...)` (straight alpha) over the frame like FrameBuffer.blend.
const BLEND = {
  color: { srcFactor: 'src-alpha', dstFactor: 'one-minus-src-alpha', operation: 'add' },
  alpha: { srcFactor: 'one', dstFactor: 'one-minus-src-alpha', operation: 'add' },
};

// floats per primitive record (UVL/GPU/Kernels.lean, `primStride`)
const PRIM_STRIDE = 36;

class GPURenderer {
  /** Compile the Lean-generated WGSL (`entries`: fragment entry point per
   * primitive kind); throws when it does not compile. */
  static async create(canvas, device, code, entries) {
    const context = canvas.getContext('webgpu');
    if (!context) throw new Error('no webgpu canvas context');
    const module = device.createShaderModule({ code });
    const info = await module.getCompilationInfo();
    const errors = info.messages.filter((m) => m.type === 'error');
    if (errors.length) {
      throw new Error(`WGSL: ${errors.map((m) => `${m.lineNum}:${m.linePos} ${m.message}`).join('; ')}`);
    }
    return new GPURenderer(canvas, device, context, module, entries);
  }

  constructor(canvas, device, context, module, entries) {
    this.name = 'gpu';
    this.device = device;
    this.context = context;
    this.format = navigator.gpu.getPreferredCanvasFormat();
    context.configure({
      device, format: this.format, alphaMode: 'opaque',
      usage: GPUTextureUsage.RENDER_ATTACHMENT | GPUTextureUsage.COPY_SRC,
    });
    const stage = GPUShaderStage.VERTEX | GPUShaderStage.FRAGMENT;
    this.layout = device.createBindGroupLayout({
      entries: [
        { binding: 0, visibility: stage, buffer: { type: 'read-only-storage' } },
        { binding: 1, visibility: stage, buffer: { type: 'read-only-storage' } },
        { binding: 2, visibility: stage, buffer: { type: 'uniform' } },
        { binding: 3, visibility: stage, buffer: { type: 'read-only-storage' } },
      ],
    });
    const layout = device.createPipelineLayout({ bindGroupLayouts: [this.layout] });
    // one pipeline per primitive kind, so fragments only run their kind's code
    this.pipelines = entries.map((entryPoint) => device.createRenderPipeline({
      layout,
      vertex: { module, entryPoint: 'vs' },
      fragment: { module, entryPoint, targets: [{ format: this.format, blend: BLEND }] },
      primitive: { topology: 'triangle-list' },
    }));
    this.screen = device.createBuffer({ size: 16, usage: GPUBufferUsage.UNIFORM | GPUBufferUsage.COPY_DST });
    this.prims = null;
    this.data = null;
    this.scene = null;
    // MSDF glyph atlas: persists across frames, glyph cells are written once
    this.atlas = device.createBuffer({ size: 16, usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST });
  }

  /** Apply the atlas updates queued by the wasm module (see web_shell.c). */
  syncAtlas(mod) {
    if (mod._uvl_gpu_atlas_reset()) {
      this.atlas.destroy();
      this.atlas = this.device.createBuffer({
        size: Math.max(16, mod._uvl_gpu_atlas_size() * 4),
        usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST,
      });
      this.bindGroup = null;
    }
    const n = mod._uvl_gpu_atlas_new_count();
    if (n) {
      const cf = mod._uvl_gpu_cell_floats();
      const glyphs = mod.HEAPF32.subarray(mod._uvl_gpu_atlas_new_glyphs() / 4, mod._uvl_gpu_atlas_new_glyphs() / 4 + n);
      const data = mod.HEAPF32.subarray(mod._uvl_gpu_atlas_new_data() / 4, mod._uvl_gpu_atlas_new_data() / 4 + n * cf);
      for (let i = 0; i < n; i++) this.device.queue.writeBuffer(this.atlas, glyphs[i] * cf * 4, data, i * cf, cf);
    }
    mod._uvl_gpu_atlas_ack();
  }

  /** A storage buffer of at least `bytes`, reallocated (and the bind group
   * rebuilt) only when it has to grow. */
  ensure(which, bytes) {
    const size = Math.max(16, Math.ceil(bytes / 16) * 16);
    if (this[which] && this[which].size >= size) return false;
    this[which]?.destroy();
    this[which] = this.device.createBuffer({
      size: Math.max(size, (this[which]?.size ?? 0) * 2),
      usage: GPUBufferUsage.STORAGE | GPUBufferUsage.COPY_DST,
    });
    this.bindGroup = null;
    return true;
  }

  /** Write `arr` to buffer `which`: only the `ranges` (flattened float
   * start/stop pairs) unless the buffer was just (re)allocated. Returns the
   * bytes written. */
  write(which, arr, ranges, full) {
    if (!arr.length) return 0;
    if (full || !ranges) {
      this.device.queue.writeBuffer(this[which], 0, arr);
      return arr.byteLength;
    }
    let bytes = 0;
    for (let k = 0; k + 1 < ranges.length; k += 2) {
      const s = ranges[k], e = Math.min(ranges[k + 1], arr.length);
      if (e > s) { this.device.queue.writeBuffer(this[which], s * 4, arr, s, e - s); bytes += (e - s) * 4; }
    }
    return bytes;
  }

  /** Draw `scene` ({prims, data: Float32Array, count, bg: [r,g,b,a]}, and
   * optionally primRanges/dataRanges: what changed since the previous scene). */
  render(scene, w, h, readback = null) {
    const { device } = this;
    const again = scene === this.scene; // the buffers already hold it
    // keep a copy for `readback`: the views on the wasm heap go stale
    if (!again) this.scene = { ...scene, prims: scene.prims.slice(), data: scene.data.slice() };
    const newPrims = this.ensure('prims', scene.prims.byteLength);
    const newData = this.ensure('data', scene.data.byteLength);
    if (!this.bindGroup) {
      this.bindGroup = device.createBindGroup({
        layout: this.layout,
        entries: [
          { binding: 0, resource: { buffer: this.prims } },
          { binding: 1, resource: { buffer: this.data } },
          { binding: 2, resource: { buffer: this.screen } },
          { binding: 3, resource: { buffer: this.atlas } },
        ],
      });
    }
    if (!again || newPrims || newData) {
      this.uploaded = this.write('prims', scene.prims, scene.primRanges, newPrims || again)
        + this.write('data', scene.data, scene.dataRanges, newData || again);
    }
    device.queue.writeBuffer(this.screen, 0, new Float32Array([w, h, 0, 0]));
    const encoder = device.createCommandEncoder();
    const target = this.context.getCurrentTexture();
    const [r, g, b] = scene.bg;
    const pass = encoder.beginRenderPass({
      colorAttachments: [{ view: target.createView(), loadOp: 'clear', storeOp: 'store', clearValue: [r, g, b, 1] }],
    });
    pass.setBindGroup(0, this.bindGroup);
    // consecutive primitives of the same kind share a draw call (paint order is kept)
    const { prims, count } = scene;
    for (let i = 0; i < count;) {
      const kind = prims[i * PRIM_STRIDE];
      let j = i + 1;
      while (j < count && prims[j * PRIM_STRIDE] === kind) j++;
      pass.setPipeline(this.pipelines[kind]);
      pass.draw(6, j - i, 0, i);
      i = j;
    }
    pass.end();
    if (readback) {
      encoder.copyTextureToBuffer({ texture: target }, { buffer: readback.buffer, bytesPerRow: readback.stride }, [w, h]);
    }
    device.queue.submit([encoder.finish()]);
  }

  /** Render the last scene again and read the canvas texture back as RGBA. */
  async readback(w, h) {
    return readTexture(this.device, this.format, w, h, (rb) => this.render(this.scene, w, h, rb));
  }
}

/** Run `draw({buffer, stride})` (which must copy the canvas texture into the
 * buffer) and return the pixels as tightly packed RGBA. */
async function readTexture(device, format, w, h, draw) {
  const stride = Math.ceil(w * 4 / 256) * 256;
  const buffer = device.createBuffer({ size: stride * h, usage: GPUBufferUsage.COPY_DST | GPUBufferUsage.MAP_READ });
  draw({ buffer, stride });
  await buffer.mapAsync(GPUMapMode.READ);
  const src = new Uint8Array(buffer.getMappedRange());
  const out = new Uint8Array(w * h * 4);
  const bgra = format === 'bgra8unorm';
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

async function createDevice(onLost) {
  if (!navigator.gpu) return null;
  const adapter = await navigator.gpu.requestAdapter();
  if (!adapter) return null;
  const device = await adapter.requestDevice();
  device.addEventListener('uncapturederror', (e) => console.error(`WebGPU: ${e.error.message}`));
  device.lost.then((info) => onLost(info.message));
  return device;
}

class WebGPUPresenter {
  static create(canvas, device) {
    const context = canvas.getContext('webgpu');
    return context ? new WebGPUPresenter(canvas, device, context) : null;
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

  /** Upload `pixels` (only the `damage` windows, when given) and draw. */
  present(pixels, w, h, damage = null, readback = null) {
    const { device } = this;
    if (!this.texture || this.texture.width !== w || this.texture.height !== h) {
      damage = null;
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
    for (const [x, y, dw, dh] of damage ?? [[0, 0, w, h]]) {
      device.queue.writeTexture({ texture: this.texture, origin: [x, y] }, pixels,
        { offset: (y * w + x) * 4, bytesPerRow: w * 4 }, [dw, dh]);
    }
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

  /** Redraw the current texture (no upload, so this checks the accumulated
   * partial uploads) and read back the canvas texture as RGBA bytes. */
  async readback(w, h) {
    return readTexture(this.device, this.format, w, h, (rb) => this.present(null, w, h, [], rb));
  }
}

class Canvas2DPresenter {
  constructor(canvas) {
    this.name = 'canvas2d';
    this.ctx = canvas.getContext('2d');
  }

  present(pixels, w, h, damage = null) {
    // a view on the wasm heap: no copy of the whole frame
    const img = new ImageData(new Uint8ClampedArray(pixels.buffer, pixels.byteOffset, w * h * 4), w, h);
    for (const [x, y, dw, dh] of damage ?? [[0, 0, w, h]]) this.ctx.putImageData(img, 0, 0, x, y, dw, dh);
  }
}

/** Start a uvl app on `canvas`. Resolves to a small control object.
 * `backend`: 'gpu' (default), 'webgpu' or 'canvas2d' (see the top of this file);
 * unavailable backends fall back to the next one. */
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
  // windows of the last frame that changed, as [x, y, w, h] (see web_shell.c)
  const damageWindows = () => {
    const p = mod._uvl_damage_ptr() / 8;
    return Array.from({ length: mod._uvl_damage_count() }, (_, i) =>
      Array.from(mod.HEAPF64.subarray(p + 4 * i, p + 4 * i + 4)));
  };
  // the primitives of the last frame, in GPU mode (views on the wasm heap)
  const gpuScene = () => ({
    prims: mod.HEAPF32.subarray(mod._uvl_gpu_prims() / 4, mod._uvl_gpu_prims() / 4 + mod._uvl_gpu_prims_len()),
    data: mod.HEAPF32.subarray(mod._uvl_gpu_data() / 4, mod._uvl_gpu_data() / 4 + mod._uvl_gpu_data_len()),
    count: mod._uvl_gpu_count(),
    bg: Array.from(mod.HEAPF32.subarray(mod._uvl_gpu_background() / 4, mod._uvl_gpu_background() / 4 + 4)),
    primRanges: mod.HEAPF32.subarray(mod._uvl_gpu_prim_ranges() / 4, mod._uvl_gpu_prim_ranges() / 4 + mod._uvl_gpu_prim_ranges_len()),
    dataRanges: mod.HEAPF32.subarray(mod._uvl_gpu_data_ranges() / 4, mod._uvl_gpu_data_ranges() / 4 + mod._uvl_gpu_data_ranges_len()),
  });
  // damaged: pixels uploaded for the last CPU frame; prims: primitives drawn
  // for the last GPU frame; leanMs: time spent in Lean for the last frame
  // uploaded: bytes of primitives and data written to the GPU for the last frame
  const state = { backend: 'none', frames: 0, damaged: 0, prims: 0, uploaded: 0, leanMs: 0, quit: false };

  // A lost WebGPU device (driver reset, or software adapters in some headless
  // browsers) falls back to Canvas 2D. A canvas that has a WebGPU context can
  // never get a 2D one, so it is swapped for a fresh element.
  let presenter = null;
  const fallBack = (why) => {
    if (presenter?.name !== 'webgpu' && presenter?.name !== 'gpu') return;
    console.warn(`WebGPU device lost (${why}); falling back to Canvas 2D`);
    const fresh = canvas.cloneNode(false);
    canvas.replaceWith(fresh);
    canvas = fresh;
    canvas.width = w;
    canvas.height = h;
    bind(canvas);
    presenter = new Canvas2DPresenter(canvas);
    state.backend = presenter.name;
    mod._uvl_set_gpu(0); // the next step rasterizes a complete frame
  };
  if (!mod._uvl_init(w, h)) throw new Error('uvl: Lean initialization failed');
  if (backend !== 'canvas2d') {
    const device = await createDevice((why) => fallBack(why)).catch((e) => {
      console.warn(`WebGPU unavailable: ${e.message}`);
      return null;
    });
    if (device && backend !== 'webgpu') {
      presenter = await GPURenderer.create(canvas, device, mod.UTF8ToString(mod._uvl_gpu_shader_source()),
        mod.UTF8ToString(mod._uvl_gpu_entry_points_source()).split(','))
        .catch((e) => { console.warn(`GPU renderer unavailable: ${e.message}`); return null; });
    }
    if (device && !presenter) presenter = WebGPUPresenter.create(canvas, device);
  }
  presenter ??= new Canvas2DPresenter(canvas);
  state.backend = presenter.name;
  mod._uvl_set_gpu(presenter.name === 'gpu' ? 1 : 0);

  const queue = [];
  const push = (kind, a = 0, b = 0, c = 0, d = 0) => queue.push(kind, a, b, c, d);
  const button = (e) => [1, 2, 3][e.button] ?? e.button + 1;
  const resizer = new ResizeObserver(() => {
    const [nw, nh] = size();
    if (nw !== w || nh !== h) push(EV.resize, nw, nh);
  });

  const pushText = (text) => { for (const ch of text) push(EV.text, ch.codePointAt(0)); };
  const pushCompose = (text) => {
    for (const ch of text) push(EV.compose, ch.codePointAt(0));
    push(EV.composeEnd);
  };

  // Text input goes through a hidden <textarea> placed over the focused field:
  // it receives input method (IME) compositions, brings up virtual keyboards
  // on touch devices, and gives the browser a real place for the caret.
  const ime = document.createElement('textarea');
  ime.setAttribute('autocapitalize', 'off');
  ime.setAttribute('autocomplete', 'off');
  ime.setAttribute('autocorrect', 'off');
  ime.spellcheck = false;
  ime.tabIndex = -1;
  Object.assign(ime.style, {
    position: 'fixed', left: '-1000px', top: '0', width: '1px', height: '1px', opacity: '0',
    padding: '0', border: '0', margin: '0', resize: 'none', overflow: 'hidden',
    fontSize: '16px', background: 'transparent', color: 'transparent', caretColor: 'transparent',
    pointerEvents: 'none', zIndex: '-1',
  });
  document.body.appendChild(ime);
  state.ime = ime;
  let keyHandled = false;

  // focus the hidden textarea while an input has focus in the app, over its bounds
  function syncInput() {
    const p = mod._uvl_input_rect();
    if (p) {
      const [x, y, rw, rh] = mod.HEAPF64.subarray(p / 8, p / 8 + 4);
      const r = canvas.getBoundingClientRect();
      const sx = r.width / w, sy = r.height / h;
      Object.assign(ime.style, { left: `${r.left + x * sx}px`, top: `${r.top + y * sy}px`,
        width: `${rw * sx}px`, height: `${rh * sy}px` });
      if (document.activeElement !== ime) ime.focus({ preventScroll: true });
    } else if (document.activeElement === ime) {
      canvas.focus({ preventScroll: true });
    }
  }

  // Accessibility: the app's semantic tree (Runtime.semantics) mirrored as
  // invisible DOM elements over the canvas, with ARIA roles, labels and
  // values. Screen readers read them; activating one clicks its centre.
  const a11y = document.createElement('div');
  Object.assign(a11y.style, { position: 'fixed', left: '0', top: '0', width: '0', height: '0',
    overflow: 'visible', pointerEvents: 'none', color: 'transparent', zIndex: '-1' });
  document.body.appendChild(a11y);
  state.a11y = a11y;
  let lastTree = null;
  function syncSemantics() {
    const r = canvas.getBoundingClientRect();
    Object.assign(a11y.style, { left: `${r.left}px`, top: `${r.top}px` });
    const tree = mod.UTF8ToString(mod._uvl_semantics());
    if (tree === lastTree) return;
    lastTree = tree;
    const sx = r.width / w, sy = r.height / h;
    a11y.replaceChildren(...tree.split('\n').filter((l) => l).map((line) => {
      const [role, label, value, checked, focused, x, y, nw, nh] = line.split('\t');
      const tag = role === 'button' ? 'button' : role === 'heading' ? 'h2' : 'div';
      const el = document.createElement(tag);
      if (tag === 'div' && role !== 'text') el.setAttribute('role', role);
      if (role === 'text' || role === 'heading' || role === 'button') el.textContent = label;
      else if (label) el.setAttribute('aria-label', label);
      if (role === 'slider') el.setAttribute('aria-valuetext', value);
      if (role === 'textbox') { el.textContent = value; if (focused === '1') el.setAttribute('aria-current', 'true'); }
      if (checked !== '-') el.setAttribute('aria-checked', checked === '1' ? 'true' : 'false');
      if (role !== 'text' && role !== 'heading' && tag !== 'button') el.tabIndex = -1;
      Object.assign(el.style, { position: 'absolute', left: `${x * sx}px`, top: `${y * sy}px`,
        width: `${nw * sx}px`, height: `${nh * sy}px`, margin: '0', padding: '0', border: '0',
        background: 'transparent', color: 'transparent', overflow: 'hidden', font: 'inherit' });
      el.dataset.uvl = role;
      // assistive technology activates elements with a click: click the app there
      el.addEventListener('click', (e) => {
        e.preventDefault();
        const cx = +x + nw / 2, cy = +y + nh / 2;
        push(EV.move, cx, cy); push(EV.down, cx, cy, 1); push(EV.up, cx, cy, 1);
        pump(performance.now());
      });
      return el;
    }));
  }

  // keyboard and clipboard events, on the canvas and on the hidden textarea
  function bindKeys(el, isText) {
    el.addEventListener('keydown', (e) => {
      if (e.isComposing || e.keyCode === 229) { keyHandled = false; return; } // the IME has it
      const code = keyCode(e);
      keyHandled = !!code;
      if (code) push(EV.keyDown, code);
      // printable keys: from the textarea's input events, or from the key here
      if (!isText && [...e.key].length === 1 && !e.ctrlKey && !e.metaKey) push(EV.text, e.key.codePointAt(0));
      if (e.key === 'Tab' || e.key.startsWith('Arrow') || e.key === 'Enter' || (!isText && e.key === ' ')) {
        e.preventDefault();
      }
    });
    el.addEventListener('keyup', (e) => { const code = keyCode(e); if (code) push(EV.keyUp, code); });
    // Clipboard. Ctrl+C / Ctrl+X reach the app as keys; the browser then fires
    // copy / cut, where the copied text is handed over synchronously (no
    // clipboard permission needed). Pasted text arrives as text input.
    const copy = (e) => {
      pump(performance.now());
      const text = takeClipboard();
      if (text) { e.clipboardData.setData('text/plain', text); e.preventDefault(); }
    };
    el.addEventListener('copy', copy);
    el.addEventListener('cut', copy);
    el.addEventListener('paste', (e) => {
      pushText(e.clipboardData?.getData('text/plain') ?? '');
      e.preventDefault();
    });
  }
  bindKeys(ime, true);
  ime.addEventListener('compositionupdate', (e) => pushCompose(e.data ?? ''));
  ime.addEventListener('compositionend', (e) => {
    pushCompose('');
    pushText(e.data ?? '');
    ime.value = '';
  });
  ime.addEventListener('input', (e) => {
    if (e.isComposing || e.inputType === 'insertCompositionText') return;
    if (e.inputType === 'insertText' && e.data) pushText(e.data);
    // virtual keyboards often delete without a key event
    else if (e.inputType === 'deleteContentBackward' && !keyHandled) {
      push(EV.keyDown, KEYS.Backspace); push(EV.keyUp, KEYS.Backspace);
    }
    ime.value = '';
  });
  // modifiers released while the page was not focused would stay down
  ime.addEventListener('blur', () => { push(EV.keyUp, KEYS.Shift); push(EV.keyUp, KEYS.Control); });

  function bind(el) {
    el.addEventListener('pointermove', (e) => push(EV.move, e.offsetX, e.offsetY));
    el.addEventListener('pointerdown', (e) => {
      el.setPointerCapture(e.pointerId);
      el.focus();
      push(EV.down, e.offsetX, e.offsetY, button(e));
      // handle the press now, so that a text field focused by it can take the
      // keyboard inside this user gesture (virtual keyboards need that)
      pump(performance.now());
    });
    el.addEventListener('pointerup', (e) => push(EV.up, e.offsetX, e.offsetY, button(e)));
    el.addEventListener('pointerleave', () => push(EV.leave));
    el.addEventListener('wheel', (e) => {
      e.preventDefault();
      const k = e.deltaMode === 1 ? 40 : e.deltaMode === 2 ? h : 1; // lines / pages to pixels
      push(EV.scroll, e.deltaX * k, e.deltaY * k);
    }, { passive: false });
    el.addEventListener('contextmenu', (e) => e.preventDefault());
    bindKeys(el, false);
    el.addEventListener('blur', () => {
      if (document.activeElement !== ime) { push(EV.keyUp, KEYS.Shift); push(EV.keyUp, KEYS.Control); }
    });
    resizer.disconnect();
    resizer.observe(el);
  }
  bind(canvas);

  let buf = 0, cap = 0, last = performance.now();

  // draw the frame produced by the last `_uvl_step`
  function draw() {
    const resized = mod._uvl_width() !== w || mod._uvl_height() !== h;
    w = mod._uvl_width();
    h = mod._uvl_height();
    if (canvas.width !== w || canvas.height !== h) { canvas.width = w; canvas.height = h; }
    if (presenter.name === 'gpu') {
      const scene = gpuScene();
      presenter.syncAtlas(mod);
      presenter.render(scene, w, h);
      state.prims = scene.count;
      state.uploaded = presenter.uploaded;
    } else {
      const damage = resized || !state.frames ? null : damageWindows();
      presenter.present(framePixels(), w, h, damage);
      state.damaged = damage ? damage.reduce((a, [, , dw, dh]) => a + dw * dh, 0) : w * h;
    }
    state.frames++;
  }

  function takeClipboard() {
    const text = mod.UTF8ToString(mod._uvl_take_clipboard());
    if (text) state.clipboard = text;
    return text;
  }

  // apply the queued events, advance animations and draw if needed
  function pump(now) {
    const n = queue.length / 5;
    if (n > cap) {
      if (buf) mod._free(buf);
      cap = Math.max(n, 64);
      buf = mod._malloc(cap * 40);
    }
    if (n) mod.HEAPF64.set(queue, buf / 8);
    queue.length = 0;
    const t0 = performance.now();
    const r = mod._uvl_step(buf, n, Math.max(0, now - last));
    last = Math.max(last, now);
    if (r === 2) { state.quit = true; return false; }
    if (r === 1) {
      state.leanMs = performance.now() - t0;
      draw();
    }
    syncInput();
    if (r === 1) syncSemantics();
    // copied without a copy event (e.g. the key was not a native shortcut)
    const text = takeClipboard();
    if (text) navigator.clipboard?.writeText(text).catch(() => {});
    return true;
  }

  function frame(now) {
    if (pump(now)) requestAnimationFrame(frame);
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
    /** The current frame rasterized by the CPU (RGBA copy); in GPU mode this
     * is the reference the GPU output is compared with. */
    snapshot() {
      const p = presenter.name === 'gpu' ? mod._uvl_render_cpu() : mod._uvl_frame_ptr();
      return p ? mod.HEAPU8.slice(p, p + w * h * 4) : null;
    },
    /** Average cost of `n` complete frames (no partial redraw): time in Lean
     * and time until the GPU finished drawing. */
    async measure(n = 30) {
      let lean = 0, total = 0;
      for (let i = 0; i < n; i++) {
        mod._uvl_set_gpu(presenter.name === 'gpu' ? 1 : 0);
        const t0 = performance.now();
        mod._uvl_step(0, 0, 0);
        const t1 = performance.now();
        draw();
        await presenter.device?.queue.onSubmittedWorkDone();
        const t2 = performance.now();
        lean += t1 - t0;
        total += t2 - t0;
      }
      return { leanMs: lean / n, frameMs: total / n };
    },
    /** What the GPU actually drew for the last frame (WebGPU backends, for tests). */
    async gpuReadback() {
      return presenter.readback ? presenter.readback(w, h) : null;
    },
  };
}
