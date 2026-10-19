import Examples.Counter
import Examples.Scenes
import Examples.Sprites
open UVL

/-- Keep `x` opaque to the compiler, so a frame of a constant scene is not
computed once as a closed term and then reused by every iteration. -/
@[noinline] def opaqueId {α : Type} (x : α) : IO α := pure x

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 20
  let w ← opaqueId 800
  let h ← opaqueId 600
  let rt := Runtime.start Examples.Counter.app w h
  let t0 ← IO.monoMsNow
  let mut s := 0
  for i in [0:n] do
    let rt ← opaqueId rt
    s := s + (rt.frame)[i]!.toNat
  let t1 ← IO.monoMsNow
  IO.println s!"counter 800x600: {(t1 - t0) / n} ms/frame ({s})"
  let ops := Layout.Widget.toOps Examples.dashboard w h
  let t0 ← IO.monoMsNow
  for i in [0:n / 4 + 1] do
    let ops ← opaqueId ops
    s := s + (Raster.render 800 600 ops).data[i]!.toNat
  let t1 ← IO.monoMsNow
  IO.println s!"dashboard 800x600: {(t1 - t0) / (n / 4 + 1)} ms/frame ({s})"
  -- partial redraw: alternate hovering two buttons, then tap one (label change)
  let rt0 := (Runtime.start Examples.Counter.app w h).present
  let pts := rt0.targets.map fun t => ((t.x + t.w / 2).toF, (t.y + t.h / 2).toF)
  let (ax, ay) := pts[0]!; let (bx, by_) := pts[1]!
  let mut rt := rt0
  let mut area := 0
  let t0 ← IO.monoNanosNow
  for i in [0:n] do
    rt := rt.handle (if i % 2 == 0 then .pointerMove ax ay else .pointerMove bx by_)
    rt := rt.present
    area := area + rt.damage.foldl (· + ·.area) 0
  let t1 ← IO.monoNanosNow
  IO.println s!"counter hover, partial redraw: {(t1 - t0).toF / n.toF / 1e6} ms/frame ({area / n} px repainted)"
  area := 0
  let t0 ← IO.monoNanosNow
  for _ in [0:n] do
    rt := rt.handle (.pointerDown ax ay .left)
    rt := rt.present
    rt := rt.handle (.pointerUp ax ay .left)
    rt := rt.present
    area := area + rt.damage.foldl (· + ·.area) 0
  let t1 ← IO.monoNanosNow
  IO.println s!"counter tap, partial redraw: {(t1 - t0).toF / (2 * n).toF / 1e6} ms/frame ({area / n} px repainted)"
  -- GPU path: what the CPU still does per frame (view → ops → primitives)
  let rtd ← opaqueId (Runtime.start Examples.Counter.app w h)
  let t0 ← IO.monoNanosNow
  let mut cnt := 0
  for _ in [0:n] do
    let rtd ← opaqueId rtd
    cnt := cnt + (GPU.Batch.build w h rtd.ops).count
  let t1 ← IO.monoNanosNow
  IO.println s!"counter, GPU lowering: {(t1 - t0).toF / n.toF / 1e6} ms/frame ({cnt / n} primitives)"
  let t0 ← IO.monoNanosNow
  for _ in [0:n] do
    let ops ← opaqueId (Layout.Widget.toOps Examples.dashboard (← opaqueId w) h)
    cnt := cnt + (GPU.Batch.build w h ops).count
  let t1 ← IO.monoNanosNow
  IO.println s!"dashboard, layout + GPU lowering: {(t1 - t0).toF / n.toF / 1e6} ms/frame"
  -- the sprites example at 1280 x 720: 300 walking units over the visible tiles
  let rtm ← opaqueId (Runtime.start (Examples.Sprites.app 1280 720) 1280 720)
  let t0 ← IO.monoNanosNow
  for _ in [0:n] do
    let rtm ← opaqueId rtm
    cnt := cnt + (rtm.handle (.tick 0.016)).model.units.size
  let t1 ← IO.monoNanosNow
  let ops := rtm.ops
  let t2 ← IO.monoNanosNow
  for _ in [0:n] do
    let rtm ← opaqueId rtm
    cnt := cnt + rtm.ops.size
  let t3 ← IO.monoNanosNow
  for _ in [0:n] do
    let ops ← opaqueId ops
    cnt := cnt + (GPU.Batch.build 1280 720 ops).count
  let t4 ← IO.monoNanosNow
  for i in [0:n / 4 + 1] do
    let ops ← opaqueId ops
    s := s + (Raster.render 1280 720 ops).data[i]!.toNat
  let t5 ← IO.monoNanosNow
  let per (a b : Nat) (k : Nat := n) : Float := (b - a).toFloat / k.toFloat / 1e6
  IO.println s!"sprites map 1280x720 ({(GPU.Batch.build 1280 720 ops).count} primitives): update {per t0 t1} ms, view {per t2 t3} ms, GPU lowering {per t3 t4} ms, CPU raster {per t4 t5 (n / 4 + 1)} ms"
  -- TrueType text: MSDF cell generation (once per glyph), then frames of text
  let font ← opaqueId (Text.uvlSans ())
  let paths := font.glyphs.map (·.path)
  let t0 ← IO.monoNanosNow
  let mut acc := 0.0
  for g in [36:56] do
    let p ← opaqueId paths[g]!
    acc := acc + (MSDF.generate p (MSDF.cellOf p))[100]!
  let t1 ← IO.monoNanosNow
  IO.println s!"MSDF cell generation: {(t1 - t0).toF / 20 / 1e6} ms/glyph ({acc})"
  let para := String.join (List.replicate 12 "The quick brown fox jumps over the lazy dog. ")
  let lines := Text.wrap font para 14 760
  let msdfOps := Text.linesOpsMSDF font lines 14 (.solid Color.black) ⟨20, 20⟩
  let outlineOps := Text.linesOps font lines 14 Color.black ⟨20, 20⟩
  s := s + (Raster.render 800 600 msdfOps).data[0]!.toNat -- warm the atlas
  for (name, ops) in [("outlines", outlineOps), ("MSDF", msdfOps)] do
    let t0 ← IO.monoNanosNow
    for i in [0:n / 4 + 1] do
      let ops ← opaqueId ops
      s := s + (Raster.render 800 600 ops).data[i]!.toNat
    let t1 ← IO.monoNanosNow
    IO.println s!"{para.length} chars of 14 px text ({name}), CPU: {(t1 - t0).toF / (n / 4 + 1).toF / 1e6} ms/frame"
