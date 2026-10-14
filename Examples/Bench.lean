import Examples.Counter
import Examples.Scenes
open UViz

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 20
  let rt := Runtime.start Examples.Counter.app 800 600
  let t0 ← IO.monoMsNow
  let mut s := 0
  for i in [0:n] do
    s := s + (rt.frame)[i]!.toNat
  let t1 ← IO.monoMsNow
  IO.println s!"counter 800x600: {(t1 - t0) / n} ms/frame ({s})"
  let ops := Layout.Widget.toOps Examples.dashboard 800 600
  let t0 ← IO.monoMsNow
  for i in [0:n / 4 + 1] do
    s := s + (Raster.render 800 600 ops).data[i]!.toNat
  let t1 ← IO.monoMsNow
  IO.println s!"dashboard 800x600: {(t1 - t0) / (n / 4 + 1)} ms/frame ({s})"
