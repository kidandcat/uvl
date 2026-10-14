// Browser smoke test for the WebAssembly build (used by CI).
//
//   node web/smoke.cjs [dist-dir] [screenshot.png]
//
// Serves web/dist, opens it in headless Chromium (WebGPU enabled through
// SwiftShader when available), waits for the first frame, clicks the first
// tap target with a real mouse event and checks that the app re-rendered.
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
    const page = await browser.newPage({ viewport: { width: 640, height: 480 } });
    page.on('console', (m) => console.log(`[page] ${m.text()}`));
    page.on('pageerror', (e) => { console.log(`[page error] ${e.message}`); failed = true; });
    await page.goto(url + (process.env.UVL_BACKEND ? `?backend=${process.env.UVL_BACKEND}` : ''));
    await page.waitForFunction(() => window.uvl && window.uvl.state.frames >= 1, null, { timeout: 30000 });
    await page.waitForTimeout(500); // a lost WebGPU device falls back to Canvas 2D
    const backend = await page.evaluate(() => window.uvl.state.backend);
    console.log(`backend: ${backend}`);

    const before = await page.evaluate(() => Array.from(window.uvl.snapshot()));
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
    const other = await page.evaluate(() => window.uvl.targetCenter(1));
    const f2 = await page.evaluate(() => window.uvl.state.frames);
    await page.mouse.move(box.x + other[0], box.y + other[1]);
    await page.waitForFunction((f) => window.uvl.state.frames > f, f2, { timeout: 10000 });
    await page.waitForTimeout(200);
    const hover = await page.evaluate(() => [window.uvl.state.damaged, window.uvl.canvas.width * window.uvl.canvas.height]);
    console.log(`hover repainted ${hover[0]} of ${hover[1]} px`);
    if (!(hover[0] > 0 && hover[0] * 10 < hover[1])) throw new Error('hover was not a partial redraw');
    const hovered = await page.evaluate(() => Array.from(window.uvl.snapshot()));

    if (backend === 'webgpu') {
      // headless Chromium does not composite WebGPU canvases into screenshots,
      // so compare what the GPU drew with the frame Lean produced instead
      const gpu = await page.evaluate(async () => Array.from(await window.uvl.gpuReadback()));
      let maxErr = 0;
      for (let i = 0; i < gpu.length; i++) if (i % 4 !== 3) maxErr = Math.max(maxErr, Math.abs(gpu[i] - hovered[i]));
      console.log(`WebGPU readback vs Lean frame: max channel error ${maxErr}`);
      if (gpu.length !== hovered.length || maxErr > 2) throw new Error('WebGPU output differs from the frame');
    }
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
