# UVL — universal visualization library

A visualization and UI library written **100% in Lean 4**: no DOM, no GTK/UIKit, no C
dependencies. Lean controls everything, from the widget tree down to the last pixel; the host
platform only has to provide a *framebuffer* and a stream of events.

![dashboard](Tests/golden/dashboard.png)

## Status

| Milestone | Contents | Status |
| --- | --- | --- |
| 1. Core and image | Verified `FrameBuffer`, SDF-based 2D primitives, Bézier paths, gradients, shadows, text, CPU rasterizer, PNG/PPM | ✅ |
| 2. Layout and DSL | *Box constraints* layout engine with invariants in the types, flex (row/col/expanded), stack, `ui!` DSL, charts | ✅ (first version) |
| 3. Desktop interactivity | Elm-style runtime (`App`, `Event`), hit testing, hover/press, SDL3 runner (~170 lines of C) | ✅ |
| 4. GPU and browser | WebGPU, Emscripten | in progress |
| Bare metal | Tiled rendering (RGB565 / 1-bit, identical to the full frame), C runtime without `libleanrt` tested on ARM Cortex-M3 (QEMU); see [`baremetal/`](baremetal/README.md) | in progress |

## Quick start

```bash
lake build              # the library
lake exe uvl-demo       # writes out/primitives.png, out/hello.png, out/dashboard.png
lake test               # golden image, layout and codec tests
lake test -- --update   # regenerate the golden images
lake exe uvl-bench      # rasterizer time per frame
lake exe uvl-counter    # desktop app (needs SDL3)
```

Requires Lean `v4.35.0` (pinned in `lean-toolchain`).

### Function API

```lean
import UVL
open UVL UI

def hello : UI.Widget Unit :=
  center <| card <| col [ row [ text "Hello", button "Click" ] ]

def main : IO Unit :=
  Image.writePNG "hello.png" (UI.render hello 320 160)
```

![hello](Tests/golden/hello.png)

### The `ui!` DSL

Indentation-based syntax: each line is `widget args*`, and `:` opens a block of children (or
`;` on the same line). It is pure sugar over the function API: `name` resolves to
`UVL.UI.name`, so adding a new widget is just defining a function.

```lean
def dashboard : UI.Widget Unit := ui! pad 20:
  col (gap := 16) (align := .stretch):
    row (gap := 12):
      text "UVL" (size := 3)
      spacer
      chip "Lean 4"
    expanded:
      card:
        lineChart [[3, 5, 4, 8, 7, 11], [1, 2, 4, 3, 6, 5]]
```

### Interactive apps (Elm architecture)

An app is `init`, a pure `update : Msg → Model → Model` and a pure
`view : Model → Widget Msg`. The runtime (also pure) takes care of layout, hit testing,
hover/press feedback and deciding when a new frame is needed. See
[Examples/Counter.lean](Examples/Counter.lean):

```lean
inductive Msg | inc | dec | reset

def view (m : Model) : UI.Widget Msg := ui! pad 24:
  card:
    row (gap := 16) (justify := .center):
      button "-" (onTap := some Msg.dec)
      text (toString m.count) (size := 6)
      button "+" (onTap := some Msg.inc)

def app : App Model Msg where
  init := {}
  update
  view
  subscriptions                      -- keyboard, ticks, ...
    | .keyDown .up, _ => some .inc
    | _, _ => none
```

![counter](Tests/golden/counter.png)

* **Desktop:** `UVL.SDL.run app` opens a window with SDL3. The C shell
  ([native/sdl_shell.c](native/sdl_shell.c)) only translates events and copies the RGBA buffer
  into a texture; there is no UI logic in C. Frames are only redrawn when something changed,
  so an idle UI costs no CPU.
* **Headless / tests:** `Runtime.simulate` feeds a script of events; the tests click around
  and compare the resulting frame with a golden image.

Building the desktop app needs SDL3 (`brew install sdl3`, or build it from the GitHub
releases). Lake finds it with `pkg-config sdl3` or in the usual prefixes. Without a display it
can be tested with
`SDL_VIDEO_DRIVER=offscreen UVL_MAX_FRAMES=2 UVL_CLICK_TARGET=1 UVL_SCREENSHOT=shot.png lake exe uvl-counter`.

### Performance

`lake exe uvl-bench` measures CPU time per frame (one core, 800×600). Two things matter most:

* The rasterizer exploits that an SDF is 1-Lipschitz: one evaluation skips whole runs of
  pixels outside the shape or fills whole runs inside it, and only the anti-aliased edge is
  evaluated pixel by pixel.
* `Float` literals are elaborated to `Float.ofBits` with the bit pattern computed at compile
  time ([Core/FloatLit.lean](UVL/Core/FloatLit.lean)); Lean compiled them as
  `Float.ofScientific`, with arbitrary-precision arithmetic on every evaluation.

### Low-level scenes (`RenderOp`)

```lean
def scene : Array RenderOp := #[
  .shadow ⟨32, 40, 200, 120⟩ 16 10 (Color.black.withAlpha 0.35),
  RenderOp.roundRect ⟨24, 28, 200, 120⟩ 16 Color.white,
  .fill (.circle ⟨320, 90⟩ 56) (.radial ⟨300, 70⟩ 80 #[(0, Color.yellow), (1, Color.red)]),
  RenderOp.path (Path.star ⟨90, 240⟩ 56 24 5) Color.yellow ]

#eval Image.writePNG "scene.png" (Raster.render 480 320 scene)
```

![primitives](Tests/golden/primitives.png)

## Architecture

```
UVL/
  Core/       Color, Vec2/Rect/Affine, fast Float literals, pixel formats
  Render/     FrameBuffer (verified), SDF, Paint, Path, Font, RenderOp, Raster, Tile
  Output/     Deflate/zlib and PNG/PPM in pure Lean
  Layout/     Constraints, Placed (positioned tree), Widget + layout engine
  UI/         widget API, ui! DSL, charts (bar, line, donut)
  App/        Event, App and Runtime (Elm architecture, hit testing)
  BareMetal/  app shell for microcontrollers (see baremetal/)
UVLWindow.lean  SDL3 shell (FFI), only used by the uvl-* window executables
native/       sdl_shell.c
baremetal/    C runtime and tooling for running UVL apps without libleanrt
Examples/     example scenes and apps, demo executable
Tests/        golden images, test PNG decoder, test driver
```

### What the types guarantee

* **No write outside the buffer.** `FrameBuffer w h` carries the proof
  `data.size = w * h * 4`; pixels are addressed with `Fin w × Fin h` and `pixel_index_lt`
  proves that every byte offset is in range. The rasterizer loops walk a `Clip w h` with
  proven bounds, so there are no bounds checks on the hot path.
* **In-place mutation.** The `FrameBuffer` is threaded from function to function with a
  unique reference, and Lean's runtime (Perceus/FBIP) mutates the `ByteArray` without copies.
* **A widget's size always respects its parent's constraints.**
  `layout w c : Result c` includes `ok : c.Admits size`
  (`minW ≤ w ≤ maxW ∧ minH ≤ h ≤ maxH`). See `Constraints.constrain_admits`.
* **No child overflows its parent.** The positioned tree `Placed s` is indexed by its size
  and every child carries the proof `x + child.w ≤ s.w ∧ y + child.h ≤ s.h`; a tree with
  overflow simply does not type-check.
* **Layout always terminates.** `layout` is a total function (well-founded recursion over
  the widget tree), not `partial`.

### Rasterizer

* Analytic shapes (rectangles, rectangles with per-corner radii, circles, ellipses, segments,
  Gaussian shadows) from their SDF: one distance evaluation per pixel and anti-aliasing for
  free.
* Paths (lines, quadratic and cubic Béziers) flattened and filled by scanline with the
  *non-zero* or *even-odd* rule, exact horizontal coverage and 4 vertical subsamples.
* Strokes with round joins and caps; nested affine transforms and clipping.
* Text with a built-in 5×7 bitmap font (ASCII plus accented letters), rasterized with exact
  area coverage at any scale. TrueType + MSDF is planned.

## Next steps

1. Milestone 4: WebGPU presenter and Emscripten build (the same `Runtime` in the browser).
2. Line-wrapping text, a TrueType parser and an MSDF atlas.
3. Stateful widgets: text field, scrolling, sliders; animations with `tick`.
4. Partial redraw (dirty regions only) for large screens.
