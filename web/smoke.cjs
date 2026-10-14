// Browser smoke test for the WebAssembly build (used by CI).
//
//   node web/smoke.cjs [dist-dir] [screenshot.png]
//
// Serves web/dist, opens it in headless Chromium (WebGPU over Vulkan when
// available), waits for the first frame, clicks the first tap target with a
// real mouse event and checks that the app re-rendered, then hovers another
// button and compares what the GPU drew with the CPU rasterizer.
// UVL_BACKEND=gpu|webgpu|canvas2d picks the backend (default: gpu),
// UVL_SIZE=WxH the canvas size, UVL_STATIC=1 skips the interaction steps
// (for apps without tap targets), and UVL_CONTROLS=1 drives the controls
// example instead (drag the slider, type in the text field, select, copy and
// paste, scroll the list).
const http = require('http');
const fs = require('fs');
const path = require('path');
const { chromium } = require('playwright');

const dist = path.resolve(process.argv[2] || path.join(__dirname, 'dist'));
const shot = process.argv[3] || path.join(dist, 'smoke.png');
const TYPES = { '.html': 'text/html', '.js': 'text/javascript', '.wasm': 'application/wasm' };

const server = http.createServer((req, res) => {
  const file = path.join(dist, decodeURIComponent(req.url.split('?')[0]) === '/' ? 'index.html' : req.url.split('?')[0]);
  if (!file.startsWith(dist) || !fs.existsSync(file)) { res.writeHead(404); res.end(); return; }
  res.writeHead(200, { 'Content-Type': TYPES[path.extname(file)] || 'application/octet-stream' });
  fs.createReadStream(file).pipe(res);
});

function diff(a, b) {
  let n = 0;
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) n++;
  return n;
}

(async () => {
  await new Promise((r) => server.listen(0, r));
  const url = `http://127.0.0.1:${server.address().port}/`;
  const browser = await chromium.launch({
    channel: process.env.UVL_CHANNEL || undefined,
    // WebGPU over Vulkan (Mesa lavapipe on CI); without it Chromium's
    // SwiftShader WebGPU device is lost immediately in headless mode
    args: process.env.UVL_CHROME_ARGS ? process.env.UVL_CHROME_ARGS.split(' ') :
      ['--enable-unsafe-webgpu', '--enable-features=Vulkan', '--use-vulkan=native',
       '--use-angle=vulkan', '--ignore-gpu-blocklist'],
  });
  let failed = false;
  try {
    const [sw, sh] = (process.env.UVL_SIZE || '480x360').split('x').map(Number);
    const page = await browser.newPage({ viewport: { width: sw + 160, height: sh + 120 } });
    page.on('console', (m) => console.log(`[page] ${m.text()}`));
    page.on('pageerror', (e) => { console.log(`[page error] ${e.message}`); failed = true; });
    const query = new URLSearchParams();
    if (process.env.UVL_BACKEND) query.set('backend', process.env.UVL_BACKEND);
    if (process.env.UVL_SIZE) query.set('size', process.env.UVL_SIZE);
    await page.goto(`${url}?${query}`);
    await page.waitForFunction(() => window.uvl && window.uvl.state.frames >= 1, null, { timeout: 30000 });
    await page.waitForTimeout(500); // a lost WebGPU device falls back to Canvas 2D
    const backend = await page.evaluate(() => window.uvl.state.backend);
    console.log(`backend: ${backend}`);

    let hovered = await page.evaluate(() => Array.from(window.uvl.snapshot()));
    if (process.env.UVL_CONTROLS) {
      const box = await page.locator('#app').boundingBox();
      // each step must produce a new, different frame
      const step = async (name, act) => {
        const before = await page.evaluate(() => Array.from(window.uvl.snapshot()));
        const f = await page.evaluate(() => window.uvl.state.frames);
        await act();
        await page.waitForFunction((n) => window.uvl.state.frames > n, f, { timeout: 10000 });
        await page.waitForTimeout(200);
        const after = await page.evaluate(() => Array.from(window.uvl.snapshot()));
        const changed = diff(before, after);
        console.log(`${name}: ${changed} bytes changed`);
        if (!changed) throw new Error(`${name} did not change the frame`);
      };
      const at = async (i) => {
        const c = await page.evaluate((k) => window.uvl.targetCenter(k), i);
        if (!c) throw new Error(`no target ${i}`);
        return [box.x + c[0], box.y + c[1]];
      };
      const [sx, sy] = await at(0); // slider (drag target)
      await step('drag the slider', async () => {
        await page.mouse.move(sx - 60, sy);
        await page.mouse.down();
        await page.mouse.move(sx + 70, sy + 40, { steps: 6 }); // captured off the track too
        await page.mouse.up();
      });
      const [tx, ty] = await at(3); // text field (input target)
      await step('type in the text field', async () => {
        await page.mouse.click(tx, ty);
        await page.keyboard.type('Hi UVL');
        await page.keyboard.press('Backspace');
      });
      await step('select with Shift+Home', () => page.keyboard.press('Shift+Home'));
      // Ctrl+C reaches the app as keys; the copied text is handed over in the
      // copy event (synthetic here, in case the native shortcut did not fire one)
      const copy = async () => {
        await page.keyboard.press('Control+c');
        return page.evaluate(() => {
          const data = new DataTransfer();
          window.uvl.canvas.dispatchEvent(new ClipboardEvent('copy', { clipboardData: data }));
          return window.uvl.state.clipboard;
        });
      };
      const copied = await copy();
      console.log(`copy: ${JSON.stringify(copied)}`);
      if (copied !== 'Hi UV') throw new Error(`copied ${JSON.stringify(copied)}, expected "Hi UV"`);
      await step('paste', async () => {
        await page.keyboard.press('End');
        await page.evaluate(() => {
          const data = new DataTransfer();
          data.setData('text/plain', ' & Lean!');
          window.uvl.canvas.dispatchEvent(new ClipboardEvent('paste', { clipboardData: data }));
        });
      });
      await page.keyboard.press('Control+a');
      const all = await copy();
      console.log(`select all + copy: ${JSON.stringify(all)}`);
      if (all !== 'Hi UV & Lean!') throw new Error(`copied ${JSON.stringify(all)} after pasting`);
      const [lx, ly] = await at(4); // scroll view
      await step('scroll the list', async () => {
        await page.mouse.move(lx, ly);
        await page.mouse.wheel(0, 150);
      });
      hovered = await page.evaluate(() => Array.from(window.uvl.snapshot()));
    } else if (!process.env.UVL_STATIC) {
      const before = hovered;
      const target = await page.evaluate(() => window.uvl.targetCenter(0));
      if (!target) throw new Error('no tap target');
      const box = await page.locator('#app').boundingBox();
      const frames = await page.evaluate(() => window.uvl.state.frames);
      const t0 = Date.now();
      await page.mouse.click(box.x + target[0], box.y + target[1]);
      await page.mouse.move(box.x + 2, box.y + 2); // leave the button so hover does not differ
      await page.waitForFunction((f) => window.uvl.state.frames > f, frames, { timeout: 10000 });
      await page.waitForTimeout(200);
      console.log(`click → new frame in ${Date.now() - t0} ms`);
      const after = await page.evaluate(() => Array.from(window.uvl.snapshot()));
      const changed = diff(before, after);
      console.log(`changed bytes after click: ${changed}`);
      if (changed === 0) throw new Error('click did not change the frame');

      // hovering another button must only repaint (and upload) a small window
      // (CPU backends), or upload only the primitives that changed (GPU)
      const other = await page.evaluate(() => window.uvl.targetCenter(1));
      const f2 = await page.evaluate(() => window.uvl.state.frames);
      await page.mouse.move(box.x + other[0], box.y + other[1]);
      await page.waitForFunction((f) => window.uvl.state.frames > f, f2, { timeout: 10000 });
      await page.waitForTimeout(200);
      const hover = await page.evaluate(() => [window.uvl.state.damaged, window.uvl.canvas.width * window.uvl.canvas.height]);
      if (backend !== 'gpu') console.log(`hover repainted ${hover[0]} of ${hover[1]} px`);
      if (backend !== 'gpu' && !(hover[0] > 0 && hover[0] * 10 < hover[1])) throw new Error('hover was not a partial redraw');
      if (backend === 'gpu') {
        const [up, total] = await page.evaluate(() => [window.uvl.state.uploaded, window.uvl.state.prims * 36 * 4]);
        console.log(`hover uploaded ${up} bytes of GPU buffers (primitive records alone: ${total} bytes)`);
        if (!(up > 0 && up < total)) throw new Error('hover did not upload incrementally');
      }
      hovered = await page.evaluate(() => Array.from(window.uvl.snapshot()));
    }

    if (backend === 'webgpu' || backend === 'gpu') {
      // headless Chromium does not composite WebGPU canvases into screenshots,
      // so compare what the GPU drew with the frame the CPU rasterizer produces
      const gpu = await page.evaluate(async () => Array.from(await window.uvl.gpuReadback()));
      let maxErr = 0, over = 0;
      for (let i = 0; i < gpu.length; i++) {
        if (i % 4 === 3) continue;
        const e = Math.abs(gpu[i] - hovered[i]);
        maxErr = Math.max(maxErr, e);
        if (e > 2) over++;
      }
      const info = await page.evaluate(() => window.uvl.state);
      console.log(`${backend} readback vs CPU frame: max channel error ${maxErr}, ${over} channels off by more than 2` +
        (backend === 'gpu' ? ` (${info.prims} primitives, ${info.leanMs.toFixed(2)} ms in Lean)` : ''));
      if (gpu.length !== hovered.length) throw new Error('readback size differs');
      // the CPU presenter must be exact; the GPU renderer differs only by f32 rounding
      if (backend === 'webgpu' ? maxErr > 2 : over * 1000 > gpu.length) throw new Error('GPU output differs from the CPU frame');
    }
    const cost = await page.evaluate(() => window.uvl.measure(30));
    console.log(`complete frame (${backend}): ${cost.leanMs.toFixed(2)} ms in Lean, ${cost.frameMs.toFixed(2)} ms until drawn`);
    await page.locator('#app').screenshot({ path: shot });
    console.log(`screenshot: ${shot}`);
  } catch (e) {
    console.error(`FAILED: ${e.message}`);
    failed = true;
  } finally {
    await browser.close();
    server.close();
  }
  process.exit(failed ? 1 : 0);
})();
