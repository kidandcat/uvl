# Sprite scene measurements (19 October 2026)

Numbers below are a snapshot of `uvl-sprites`, not a promise about the
current renderer. They were taken on 19 October 2026, before hardware-sampled
instanced sprites, static sprite layers, and the cheaper `Batch.build` that
landed on 23 October 2026. Re-measure before treating a figure as current.

The scene is a 64×64 tile map (a 2048×2048 world) with walking units, drawn
with textured quads. The same sampling path exists on the CPU rasterizer and
in the GPU kernels.

## Desktop

Apple M1 Pro, Metal, 1280×720 window.
`UVL_STATS=1`, optionally `UVL_PRESENT=immediate`, then
`lake exe uvl-sprites` with a unit count and a zoom. "lower" is Lean turning
render ops into GPU primitives. "present" is upload, submit, and present
(Fifo includes the vsync wait).

| Scene | Present mode | fps | step | view | lower | upload + submit + present |
| --- | --- | --- | --- | --- | --- | --- |
| 300 units, zoom 1 (about 1 290 primitives) | Fifo (vsync) | 60.0 steady | 0.05 ms | 0.24 ms | 0.93 ms | 15.4 ms (vsync wait) |
| 300 units, zoom 1 | immediate | about 285 | 0.03 ms | 0.24 ms | 0.92 ms | 2.3 ms |
| 300 units, zoom 0.35 (whole map, about 4 400 tiles) | immediate | about 180 | 0.03 ms | 0.84 ms | 3.1 ms | 1.6 ms |
| 1 000 units, zoom 1 | immediate | about 281 | 0.04 ms | 0.36 ms | 1.4 ms | 1.7 ms |
| 1 000 units, zoom 0.35 | immediate | about 156 | 0.05 ms | 0.95 ms | 3.6 ms | 1.8 ms |
| 3 000 units, zoom 1 | immediate | about 187 | 0.06 ms | 0.72 ms | 2.8 ms | 1.8 ms |
| 3 000 units, zoom 0.35 (all on screen) | immediate | about 105 | 0.1 ms | 1.3 ms | 5.2 ms | 2.8 ms |
| 3 000 units, zoom 0.35 | Fifo | 60.0 | | | | |
| 300 units, zoom 1, CPU rasterizer (`UVL_RENDERER=cpu UVL_VSYNC=0`) | | about 2.5–3 | 0.06 ms | 335 ms (view + raster) | | 0.7 ms |

`lake exe uvl-bench` on that machine agreed: update 0.004 ms, view 0.23 ms,
GPU lowering 0.88 ms, CPU raster about 400 ms for the 1280×720 map.

Before the batch arrays stopped being copied on every primitive, lowering
took 7.5–8.6 ms per frame and immediate mode topped out near 117 fps.

## Android emulator

arm64 system image on the same M1, Pixel-class 1080×2400 at 420 dpi. The app
renders at density-independent size (411×914 buffer, 411×841 below the status
bar), 300 units, zoom 1.

Build `Examples.SpritesAndroid`, then:

```sh
adb shell setprop debug.uvl.stats 1
adb logcat -s uvl
```

| Renderer | fps | present per frame |
| --- | --- | --- |
| GPU: wgpu-native, Vulkan, SwiftShader (software Vulkan on the host CPU) | about 44 | about 22 ms |
| CPU rasterizer (`setprop debug.uvl.cpu 1`) | about 1.6 | about 620 ms |

The emulator has no GPU, so the 22 ms is a software renderer shading every
fragment. A real phone was not attached for these numbers. To record one:

```sh
android/build.sh Examples.SpritesAndroid
adb install -r android/dist/uvl-example.apk
adb shell setprop debug.uvl.stats 1
adb shell am start -n io.github.kidandcat.uvl/android.app.NativeActivity
adb logcat -s uvl
```

`adb logcat` prints `renderer: GPU on <adapter>`, then the fps lines. The
in-app fps HUD is not that number: the shell clamps `dt` to 100 ms, so the
HUD saturates at 10 fps.

## Limits observed with that build

- The CPU rasterizer is the wrong path for this scene: about 2.5 fps at 720p
  on an M1, about 1.6 fps on the emulator.
- One sprite texture per frame. The batch uploads a single texture and
  replaces it when the id changes. Several atlases in one frame need a
  texture array or a larger atlas.
- Texture ids are compared by value and the GPU upload cache keys on them.
  A reused id draws the wrong sheet.
- At zoom 0.35 the window self-check (screenshot plus GPU) reported 0.14% of
  channels off, above a 0.1% threshold, max error 22/255. That was `f32`
  versus `f64` in nearest sampling at world coordinates near 2 000. Moving
  the camera by 1e-4 world units changed 1 327 channels on the CPU alone.
  Large maps want camera-relative coordinates.
- The web shell forwarded touch and pinch events and did not upload sprite
  textures yet.
- Android GPU rendering used the density-independent buffer (411×914), not
  the native resolution. `debug.uvl.present immediate` did not change the
  emulator timings, which were SwiftShader-bound.
- The example units walk over water. There is no pathfinding, selection, or
  game logic in that sample.
