import Examples.Scenes
import Examples.Counter

/-!
Tile renderer checks: a frame assembled from tiles must be bit-identical to the
full-frame render, for several tile shapes (including ones that do not divide
the frame, so edge tiles are clipped).
-/

namespace Tests.Tile
open UVL

structure Scene where
  name : String
  w : Nat
  h : Nat
  ops : Array RenderOp
  bg : Color

def counterScene : Scene :=
  let rt := Runtime.start Examples.Counter.app 320 240
  ⟨"counter", 320, 240, rt.tree.2.toOps 0 0 rt.pointerState, rt.app.background⟩

def scenes : List Scene := [
  ⟨"primitives", 480, 320, Examples.primitives, Color.white⟩,
  ⟨"hello", 320, 160, Examples.hello.toOps 320 160, Color.hex 0xECEFF1⟩,
  ⟨"dashboard", 800, 600, Examples.dashboard.toOps 800 600, Color.hex 0xF5F7FA⟩,
  counterScene
]

def tileShapes : List (Nat × Nat) := [(64, 16), (32, 32), (37, 23), (1, 240), (4096, 4096)]

def check (name : String) (cond : Bool) : IO Bool := do
  IO.println s!"  [{if cond then "ok" else "FAIL"}] {name}"
  return cond

/-- Largest per-byte difference and number of differing bytes. -/
def diffStats (a b : ByteArray) : Nat × Nat := Id.run do
  let mut m := 0
  let mut n := 0
  for i in [0:Min.min a.size b.size] do
    let x := a[i]!.toNat; let y := b[i]!.toNat
    let d := if x > y then x - y else y - x
    if d > 0 then n := n + 1
    m := Max.max m d
  return (m, n)

/-- Fixed-point distances on a grid of sample points vs the `Float` formulas. -/
def q16MatchesFloat : Bool := Id.run do
  let q := Q16.ofFloat
  let mut ok := true
  for i in [0:60] do
    for j in [0:40] do
      let px := i.toFloat * 7.3 - 20.0
      let py := j.toFloat * 5.1 - 10.0
      let c := Scalar.circle (q px) (q py) (q 150.25) (q 90.5) (q 37.75)
      let cf := Scalar.circle px py 150.25 90.5 37.75
      let b := Scalar.roundedBox (q px) (q py) (q 200.0) (q 100.0) (q 120.5) (q 60.0)
        (q 0.0) (q 12.0) (q 30.0) (q 6.5)
      let bf := Scalar.roundedBox px py 200.0 100.0 120.5 60.0 0.0 12.0 30.0 6.5
      if (c.toFloat - cf).abs > 1.0 / 16384.0 || (b.toFloat - bf).abs > 1.0 / 16384.0 then
        ok := false
  return ok

def run : IO Bool := do
  let mut ok := true
  for s in scenes do
    let full := Raster.render s.w s.h s.ops s.bg
    let mut same := true
    for (tw, th) in tileShapes do
      if (Tile.renderTiled s.w s.h tw th s.ops s.bg).data != full.data then
        same := false
        IO.println s!"    {s.name}: tiles {tw}x{th} differ from full frame"
    ok := (← check s!"{s.name}: tiled == full frame, bit for bit ({tileShapes.length} tile shapes)" same) && ok
    let rgb := Tile.renderTiledRGB565 s.w s.h 64 16 s.ops s.bg
    ok := (← check s!"{s.name}: RGB565 tiles == RGB565 of full frame" (rgb == full.toRGB565)) && ok
  -- Q16.16 fixed-point path
  for s in scenes do
    let float := Raster.render s.w s.h s.ops s.bg
    let full := Raster.render s.w s.h s.ops s.bg (fixed := true)
    let mut same := true
    for (tw, th) in tileShapes do
      if (Tile.renderTiled s.w s.h tw th s.ops s.bg (fixed := true)).data != full.data then
        same := false
        IO.println s!"    {s.name}: fixed-point tiles {tw}x{th} differ from full frame"
    ok := (← check s!"{s.name}: fixed point, tiled == full frame ({tileShapes.length} tile shapes)" same) && ok
    let (maxDiff, changed) := diffStats float.data full.data
    ok := (← check s!"{s.name}: fixed point vs Float: max channel diff {maxDiff}, {changed} bytes differ" (maxDiff ≤ 2)) && ok
  ok := (← check "Q16 SDFs match Float within 2^-14 px" q16MatchesFloat) && ok
  -- pixel format sanity
  let fb := Raster.render 37 21 Examples.primitives
  let mono := fb.toMonoPages
  let back := (FrameBuffer.ofMonoPages 37 21 mono).toMonoPages
  ok := (← check "mono pages: size and re-pack round trip" (mono.size == 3 * 37 && back == mono)) && ok
  let rows := fb.toMonoRows
  ok := (← check "mono rows: size" (rows.size == 5 * 21)) && ok
  let preview := FrameBuffer.ofRGB565 37 21 fb.toRGB565
  ok := (← check "RGB565 preview re-encodes identically" (preview.toRGB565 == fb.toRGB565)) && ok
  return ok

end Tests.Tile
