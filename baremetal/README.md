# UVL on microcontrollers

The same Lean app that runs on the desktop (`Examples/Counter.lean`), compiled
to C and run without `libleanrt`, without an operating system and without a
system heap. It is tested automatically on x86-64, i386 and ARM Cortex-M3
(QEMU); all three produce frames byte-identical to the native Lean binary.

```
baremetal/
  include/uvl.h          C ABI between the firmware and the Lean app
  include/lean/config.h  replaces the toolchain's config.h (no mimalloc, 32-bit)
  rt/uvl_rt.c            minimal runtime: static pool, RC, closures, arrays, strings, small Nat/Int
  rt/uvl_shell.c         wrappers that borrow the state (render a tile into a DMA buffer)
  tools/uvl_bundle.py    gathers the generated C + reachable Init/Std into a compilable bundle
  tools/gen_c.sh         generates C for toolchain modules (Init/Std/Lean ship only as .a)
  tools/test.sh          end-to-end test (64/32-bit host + QEMU)
  host/main.c            harness: applies events and streams frames tile by tile
  qemu/                  startup + linker script for mps2-an385 (Cortex-M3)
```

## How it works

1. **Lean side.** `UVL/BareMetal/Shell.lean` wraps an `App` together
   with its model, the current scene split into tiles (`TileList`) and the
   screen configuration. `Examples/BareMetalCounter.lean` exports the C API with
   `@[export]`: `uvl_init`, `uvl_event`, `uvl_needs_redraw`, `uvl_begin_frame`,
   `uvl_tile_rgb565` and `uvl_tile_mono`.
2. **Bundle.** `uvl_bundle.py` takes the C that `lake` generates and adds the
   C of the Init/Std modules that are actually used, linking and iterating with
   `--gc-sections` until it reaches a fixpoint. It then rewrites the module
   initializers so they only initialize reachable constants (`uvl_init.c`). The
   output is `src/*.c`, `rt/*.c` and `include/`, plus `uvl_bundle.cmake` for
   Pico SDK or ESP-IDF.
3. **Firmware.** The main loop is the one in `include/uvl.h`: it turns button
   or touch events into `uvl_event` calls. When a redraw is needed it renders
   tile by tile (64×16 by default) into one of two buffers while the other one
   is sent over DMA.

### Memory: a static pool, not a per-frame arena

The original plan proposed a 16 KB arena reset every frame. We did not do
that because, with Lean's reference counting, a tile's temporaries are freed
as soon as they are no longer used, so peak memory does not grow with the
number of tiles. A blind reset would also destroy the UI state (model and
scene) that lives across frames.

`uvl_rt.c` uses a static pool (`UVL_HEAP_SIZE`, 96 KB by default) with 8-byte
size classes up to 512 B (O(1) free lists), best-fit for larger blocks, and
defragmentation when it runs out of memory. It never calls `malloc`.
`uvl_heap_stats()` reports usage.

Measured with the counter at 320×240 on 32 bits, 64×16 tiles:

| | |
| --- | --- |
| Live after `uvl_rt_init` + `uvl_init` | ~38 KB (closed constants, incl. ~23 KB glyph table) |
| Peak live memory while rendering | ~62 KB |
| Pool high-water mark (including fragmentation) | ~71 KB of 96 KB |
| ARM code (Thumb-2, `-O2`) | ~347 KB of `.text` including newlib + semihosting |

That fits an RP2040 (264 KB SRAM, 2 MB flash) and an ESP32. Most of the
post-init footprint is `Font.glyphTable`, built as an `Array` at startup;
moving it to static data in flash would save ~23 KB of RAM and is the next
obvious optimization.

### 32-bit details

- `include/lean/config.h` defines `LEAN_EMSCRIPTEN` on 32-bit targets.
  `lean.h` only uses that macro to split 8-byte scalar literals into two words.
- The Lean compiler assumes `Nat` literals below 2^63 are scalars and never
  `dec`s them. On 32 bits some of them (e.g. `9007199254740992` in the `Float`
  model) are heap objects. To avoid leaking them, the bundler turns them into
  interned persistent literals (`uvl_nat_literal`).
- Big `Nat`/`Int` values are implemented with a 64-bit magnitude. A
  computation that leaves that range is a fatal panic; UVL's code never does.
- No `Task`s, file IO or threads; the app does not need them.

## Running the test

```sh
baremetal/tools/test.sh
```

The script:

1. Builds `Examples` and `uvl-baremetal-ref`, the native Lean reference.
2. Generates, the first time only, the C for Init in `.lake/baremetal/init-c`
   (about 3 minutes).
3. Creates the bundle in `.lake/baremetal/bundle`.
4. Compares `frame0`/`frame1.rgb565` against the reference in three builds:
   - 64-bit host;
   - 32-bit host (`gcc -m32`) with a 96 KB pool;
   - Cortex-M3 under QEMU, when `arm-none-eabi-gcc` and `qemu-system-arm` are installed.

To use the bundle in another project, include `uvl_bundle.cmake` and compile
`UVL_BUNDLE_SOURCES` with `UVL_BUNDLE_INCLUDE` ahead of the Lean toolchain's
include directory. There is no need to link against `libleanrt` or `libInit`.
