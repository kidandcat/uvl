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
