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
