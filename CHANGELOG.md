# Changelog

All notable changes to this project are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.1.0] - 2026-10-29

First version number. Everything below landed on `main` between 2026-10-14
and 2026-10-23 with no package version, git tag, or GitHub release. Lake's
default for a package that sets no version is `0.0.0`; `0.1.0` is the first
version this repository actually declares. It is a development version
(`0.x`): source compatibility is not promised between minor numbers.

No `v0.1.0` tag and no GitHub release were created when this version was
added. See [RELEASING.md](RELEASING.md).

### Added

- Verified `FrameBuffer`, SDF primitives, Bézier paths, gradients, shadows,
  bitmap text, a CPU rasterizer, and PNG/PPM output.
- Box-constraints layout (total, by well-founded recursion on the widget
  tree), the `ui!` DSL, charts, golden image tests, and GitHub Actions CI.
- Widgets generic over the application message type. Elm-style `App` runtime
  with one event type, hit testing, and headless simulation. SDL3 desktop
  shell.
- Browser host: Lean runtime and `Init` compiled to WebAssembly, WebGPU
  presenter, Canvas 2D fallback, DOM events.
- GPU rendering: a typed WGSL DSL, shader kernels, lowering of render ops,
  one pipeline per primitive kind, on the web and on desktop through
  wgpu-native. Incremental uploads of primitive and data ranges.
- TrueType parser, embedded UVL Sans, kerning, wrapping, `label` and
  `paragraph`. MSDF atlas generated in Lean and sampled the same way on the
  CPU and the GPU.
- Controls: pointer capture, focus, wheel routing, slider, checkbox, text
  field, scroll view. Runtime clock, caret blink, hover fade, `Tween`.
  Text selection, word navigation, multi-line `textArea`, undo/redo, system
  clipboard, IME composition on web and desktop.
- Semantic tree and an ARIA mirror of it in the browser.
- Android `NativeActivity` APK (no Java), touch, on-screen keyboard, density
  and insets, and a Vulkan path through wgpu-native for apps that import
  `UVLGPU`. GPU on Android has been tried on the emulator only.
- Compile-time HTML-like markup. PNG decoder in the library.
- Sprites (textured quads), a camera with pan and pinch zoom, and the
  `uvl-sprites` example. Later: hardware-sampled instanced sprites, static
  sprite layers, and a scaled world target.
- Bare metal, still in progress: tiled RGB565 and 1-bit rendering that
  matches the full frame, a C runtime without `libleanrt`, QEMU on Cortex-M3,
  Pico SDK and ESP-IDF firmware, and a LilyGO T-Display stopwatch.
- Partial redraw. Proofs that pixels outside a damage window stay unchanged,
  and that the render-path recursions terminate.

### Changed

- The library is named UVL. Documentation and example prose are in English.
- Faster solid span fills, faster MSDF sampling, and a bitmap font that stays
  in flash on the bare-metal link.
- On macOS the process keeps Lean's `main` on the main thread so SDL can open
  a window.
