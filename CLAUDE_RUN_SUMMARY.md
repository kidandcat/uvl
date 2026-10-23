# Spike: can uvl carry a Reinos-style RTS, 100 % Lean?

Branch `claude/spike-sprites-2026-10-19` (not pushed, no PR). Every commit builds with
`lake build` and passes `lake test`; no new `sorry`.

## What was done

| Step | Commit(s) | Result |
|---|---|---|
| 1. Android build at HEAD | `5be8baa` | Builds on macOS again: stubs for symbols Lean/Std export under C names, arm64 launch fixed; phone example passes `android/smoke.sh` on the emulator. |
| 2. Sprite/atlas op | `669a5c2`, `c9431d9` | `RenderOp.sprites tex quads smooth`: textured quads (nearest or bilinear), same sampling code path on the CPU rasterizer and in the WGSL kernel. Golden test GPU (interpreted shader) vs CPU; `uvl-gpu-check` compares the real GPU with the CPU. |
| 3. Camera + multitouch | `554ab55` | `UVL.Game.Camera` (world↔screen, `zoomAt`, `clampTo`) and `UVL.Game.Gestures` (one finger / mouse drag pans, two-finger pinch zooms around the midpoint and pans, wheel pans, Ctrl+wheel and trackpad pinch zoom). Pure Lean; shells only forward `touchDown/Move/Up` (with finger id) and `pinch` events (SDL, Android, web). 15 tests in `Tests/Camera.lean`. |
| 4. PNG decoder into the library | `f16ba28` | `UVL.Output` decodes PNG, so atlases can be loaded from image files (the example generates its atlas in Lean). |
| 5. `uvl-sprites` example | `e674f39` | 64×64 tile map (2048×2048 world, atlas generated in Lean), 300 units walking to random targets, y-sorted, culled to the view, animated walk frames, HUD with fps. Golden `Tests/golden/map.png` and a map scene in `uvl-gpu-check`. |
| 6. Measuring | `7a25177`, `6ae58e8`, `a499f61` | `UVL_STATS=1` (desktop) and `debug.uvl.stats` (Android) frame statistics; vsync-free presentation for measuring; a 10× speed-up of the GPU lowering (it copied the batch arrays on every primitive). |
| 7. GPU on Android | `e4d933c` | wgpu-native (prebuilt Android release) over Vulkan, same WGSL and Lean lowering as desktop/web; CPU fallback. Survives background/foreground (surface recreated). |
| Docs | `18d05cc` | README and `android/README.md`. |

Also fixed on the way: on macOS, Lean runs `main` on a secondary thread unless
`LEAN_MAIN_USE_THREAD=0`, and Cocoa refuses to open windows there (SDL says "No available
video device"); `native/sdl_shell.c` now sets it in a constructor (`308f18c`).

## Measurements

### Desktop: Apple M1 Pro, Metal, 1280×720 window

How: `UVL_STATS=1 [UVL_PRESENT=immediate] lake exe uvl-sprites [units] [zoom%]` (or
`.lake/build/bin/uvl-sprites`), steady-state line after a few seconds. "lower" is Lean turning
the render ops into GPU primitives; "present" is upload + submit + present (with Fifo it
includes the vsync wait).

| Scene | Present mode | fps | step | view | lower | upload+submit+present |
|---|---|---|---|---|---|---|
| 300 units, zoom 1 (≈1 290 primitives) | Fifo (vsync) | **60.0** steady | 0.05 ms | 0.24 ms | 0.93 ms | 15.4 ms (vsync wait) |
| 300 units, zoom 1 | immediate | **≈285** | 0.03 ms | 0.24 ms | 0.92 ms | 2.3 ms |
| 300 units, zoom 0.35 (whole map, ≈4 400 tiles) | immediate | ≈180 | 0.03 ms | 0.84 ms | 3.1 ms | 1.6 ms |
| 1 000 units, zoom 1 | immediate | ≈281 | 0.04 ms | 0.36 ms | 1.4 ms | 1.7 ms |
| 1 000 units, zoom 0.35 | immediate | ≈156 | 0.05 ms | 0.95 ms | 3.6 ms | 1.8 ms |
| 3 000 units, zoom 1 | immediate | ≈187 | 0.06 ms | 0.72 ms | 2.8 ms | 1.8 ms |
| 3 000 units, zoom 0.35 (all on screen) | immediate | ≈105 | 0.1 ms | 1.3 ms | 5.2 ms | 2.8 ms |
| 3 000 units, zoom 0.35 | Fifo | **60.0** | | | | |
| 300 units, zoom 1, **CPU rasterizer** | `UVL_RENDERER=cpu UVL_VSYNC=0` | **≈2.5–3** | 0.06 ms | 335 ms (view + raster) | – | 0.7 ms |

`lake exe uvl-bench` agrees: update 0.004 ms, view 0.23 ms, GPU lowering 0.88 ms, CPU raster
≈400 ms for the 1280×720 map.

Before `7a25177` the lowering took 7.5–8.6 ms per frame (quadratic `FloatArray` copies:
`{ b with prims := b.prims.push … }` copies, because the field is still shared with `b`); that
alone capped immediate mode at ≈117 fps.

### Android: emulator (arm64 system image on the M1, Pixel-class 1080×2400 at 420 dpi)

How: `android/build.sh Examples.SpritesAndroid`, `adb shell setprop debug.uvl.stats 1`, launch,
`adb logcat -s uvl`. The app renders at density-independent size (411×914 buffer, app 411×841
below the status bar), 300 units, zoom 1 (≈150 units on screen).

| Renderer | fps | present per frame |
|---|---|---|
| GPU: wgpu-native → Vulkan → **SwiftShader** (software Vulkan on the host CPU) | **≈44** | ≈22 ms |
| CPU rasterizer (`setprop debug.uvl.cpu 1`) | **≈1.6** | ≈620 ms |

The emulator has no GPU: its Vulkan is SwiftShader, so the 22 ms is a software renderer
shading every fragment on the CPU. Lean's share of a frame (step + view + lowering) is about
1.2 ms on the M1 at 720p (the emulator runs arm64 code at native speed on it).

**Not measured: a real phone.** None was connected during the run (`adb devices` only listed
the emulator), so the analysis' go/no-go criterion (60 fps on a real phone) is still open. To
close it with a phone plugged in:

```sh
android/build.sh Examples.SpritesAndroid          # APK in android/dist (UVL_APK to rename)
adb install -r android/dist/uvl-example.apk
adb shell setprop debug.uvl.stats 1
adb shell am start -n io.github.kidandcat.uvl/android.app.NativeActivity
adb logcat -s uvl                                  # "renderer: GPU on <adapter>", then fps lines
```

## What did not work / limitations found

- **CPU rasterizer is not an option for a game**: ≈2.5 fps at 720p on an M1 and ≈1.6 fps on
  the emulator. Everything game-like has to go through the GPU path (desktop, web, Android).
- **One texture per frame on the GPU** (the batch carries a single sprite texture, re-uploaded
  when its id changes). Fine for one atlas; several atlases per frame need texture arrays or
  a bigger atlas.
- **Texture ids must be unique per process**: textures compare by `id` and the GPU upload cache
  keys on it (a collision rendered the map with the unit sheet).
- **GPU vs CPU at zoom 0.35**: the window's self-check (`UVL_SCREENSHOT` + GPU) reports 0.14 % of
  channels off (threshold 0.1 %, max error 22/255). It is f32 vs f64 in nearest sampling at
  world coordinates ≈2 000: moving the camera by 1e-4 world units changes 1 327 channels on
  the CPU alone. Invisible, but large maps want camera-relative coordinates.
- **Web shell**: forwards touch/pinch events but does not upload sprite textures yet, and was
  only checked with `node --check` (no Emscripten here).
- **Android**: the in-app fps HUD saturates at 10 fps because the shell clamps `dt` to 100 ms
  (the logcat stats are the real numbers). GPU rendering uses the density-independent buffer
  (411×914), not native resolution; native resolution is a scale transform away but untested.
  The emulator's `debug.uvl.present immediate` made no difference (SwiftShader-bound).
- **Example only**: units walk over water (no pathfinding), there is no selection or game logic.

## Recommendation on F1 (game core)

**Go ahead with F1**, with one cheap check first: run the command above on a real phone (it takes
minutes). Why:

- **The architecture holds, with no game logic in C.** Logic, camera, gestures, lowering and
  shaders are Lean; the shells only forward events and pixels.
- **Lean's cost per frame is small.** It is about 1.2 ms of the 16.7 ms budget at 300 units, and
  about 6.5 ms at 3 000 units with everything on screen. A phone CPU 3–4× slower than an M1 core
  still fits 300–1 000 units in a 60 fps frame.
- **The renderer is not a bottleneck on real GPUs.** Metal runs the scene at about 285 fps uncapped.
  On Android the full path (Vulkan surface, Lean lowering, WGSL) works end to end. The only slow
  part was SwiftShader, which a real phone doesn't use.
- **F1 doesn't depend on the renderer.** The game core (state, orders, economy, combat, bot, A*,
  theorems) is pure Lean. If the phone check fails, the verified core can drive another client,
  as the analysis already says.

What to fold into F1 or soon after, based on what the spike showed:

- incremental lowering, or moving the static tile layer into a cached GPU buffer (at full zoom-out, tiles dominate lowering);
- camera-relative coordinates for large maps;
- several textures per frame;
- texture upload in the web shell;
- native-resolution rendering on Android.
