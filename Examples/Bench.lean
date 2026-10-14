import Examples.Counter
import Examples.Scenes
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
