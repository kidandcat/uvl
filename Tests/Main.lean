import Examples.Scenes
import Examples.Counter
import Examples.Sprites
import Tests.PngDecode
import Tests.Tile
import Tests.Damage
import Tests.GPU
import Tests.Text
import Tests.Controls
import Tests.Html
import Tests.Camera

/-!
Test driver (`lake test`).

* Golden images: each scene is rendered and compared with `Tests/golden/<name>.png`
  (decoded, with a tiny per-channel tolerance so the suite is robust to last-ulp
  differences of libm across platforms). Run `lake test -- --update` to regenerate.
* Layout checks: concrete positions for the roadmap example, and the
  `Admits` invariant re-checked at runtime over a sweep of constraints.
* Codec checks: PNG round-trip through our encoder and the test decoder.
-/

open UVL UVL.Layout

structure Golden where
  name : String
  w : Nat
  h : Nat
  png : Unit → ByteArray

/-- Script of events exercising the counter app. -/
def clickOn {Model Msg : Type} [BEq Msg] (rt : Runtime Model Msg) (m : Msg) : List Event :=
  match rt.targets.toList.find? (fun t => t.tapMsg?.any (· == m)) with
  | some t => Runtime.click (t.x + t.w / 2).toF (t.y + t.h / 2).toF
  | none => []

def counterAfterClicks : Runtime Examples.Counter.Model Examples.Counter.Msg := Id.run do
  let mut rt := Runtime.start Examples.Counter.app 480 360
  for m in [Examples.Counter.Msg.inc, .inc, .inc, .dec, .inc] do
    rt := rt.simulate (clickOn rt m)
  -- the hover feedback has faded in
  return rt.simulate [.keyDown (.char '+'), .tick 0.2]

/-- The sprites example after a two-finger pinch and half a second of walking. -/
def mapSession : Runtime Examples.Sprites.Model Examples.Sprites.Msg :=
  (Runtime.start (Examples.Sprites.app 400 240 300 0.8) 400 240).simulate
    [.touchDown 1 100 120, .touchDown 2 300 120, .touchMove 2 340 120, .touchMove 1 80 120,
     .touchUp 1 80 120, .touchUp 2 340 120, .tick 0.5]

def goldens : List Golden := [
  ⟨"primitives", 480, 320, fun _ => Image.toPNG (Raster.render 480 320 Examples.primitives)⟩,
  ⟨"hello", 320, 160, fun _ => Image.toPNG (UI.render Examples.hello 320 160 (Color.hex 0xECEFF1))⟩,
  ⟨"dashboard", 800, 600, fun _ =>
    Image.toPNG (UI.render Examples.dashboard 800 600 (Color.hex 0xF5F7FA))⟩,
  ⟨"counter", 480, 360, fun _ => counterAfterClicks.framePNG⟩,
  ⟨"typography", 460, 280, fun _ =>
    Image.toPNG (UI.render Examples.typography 460 280 (Color.hex 0xECEFF1))⟩,
  ⟨"msdf", 560, 260, fun _ => Image.toPNG (Raster.render 560 260 Examples.msdfText)⟩,
  ⟨"sprites", 240, 160, fun _ => Image.toPNG (Raster.render 240 160 Examples.spriteScene)⟩,
  ⟨"controls", 960, 360, fun _ => Tests.Controls.session.framePNG⟩,
  ⟨"map", 400, 240, fun _ => mapSession.framePNG⟩
]

/-- Max channel difference allowed, and fraction of bytes allowed to differ. -/
def tolerance : Nat := 2

def compare (a b : ByteArray) : Nat × Nat := Id.run do
  let mut maxDiff := 0
  let mut nDiff := 0
  for i in [0:a.size] do
    let x := a[i]!.toNat; let y := b[i]!.toNat
    let d := if x > y then x - y else y - x
    if d > 0 then nDiff := nDiff + 1
    if d > maxDiff then maxDiff := d
  return (maxDiff, nDiff)

def checkGolden (update : Bool) (g : Golden) : IO Bool := do
  let path : System.FilePath := s!"Tests/golden/{g.name}.png"
  let actual := g.png ()
  if update || !(← path.pathExists) then
    IO.FS.writeBinFile path actual
    IO.println s!"  [updated] {g.name}"
    return true
  let expected ← IO.FS.readBinFile path
  if expected == actual then
    IO.println s!"  [ok] {g.name} (byte-identical)"
    return true
  match Image.decodePNG expected, Image.decodePNG actual with
  | .ok (ew, eh, ed), .ok (aw, ah, ad) =>
    if ew != aw || eh != ah then
      IO.println s!"  [FAIL] {g.name}: size {aw}x{ah}, expected {ew}x{eh}"
      return false
    let (maxDiff, nDiff) := compare ed ad
    if maxDiff <= tolerance then
      IO.println s!"  [ok] {g.name} ({nDiff} bytes within ±{tolerance})"
      return true
    IO.FS.createDirAll "Tests/out"
    IO.FS.writeBinFile s!"Tests/out/{g.name}.png" actual
    IO.println s!"  [FAIL] {g.name}: {nDiff} bytes differ, max Δ {maxDiff}; see Tests/out/{g.name}.png"
    return false
  | .error e, _ | _, .error e =>
    IO.println s!"  [FAIL] {g.name}: decode error {e}"
    return false

def check (name : String) (cond : Bool) : IO Bool := do
  IO.println s!"  [{if cond then "ok" else "FAIL"}] {name}"
  return cond

def layoutTests : IO Bool := do
  let rects := (layout Examples.hello (Constraints.tight ⟨320, 160⟩)).node.rects 0 0
  let t1 ← check "hello: card centered, row content placed" (rects ==
    [(0, 0, 320, 160), (68, 49, 184, 62), (68, 49, 184, 62), (84, 65, 152, 30), (84, 65, 152, 30),
     (84, 73, 58, 14), (150, 65, 86, 30), (150, 65, 86, 30), (164, 73, 58, 14)])
  -- Re-check the (already proved) Admits invariant at runtime over a sweep.
  let widgets : List (UI.Widget Unit) := [Examples.hello, Examples.dashboard, UI.text "overflowing text that is long",
    UI.row [UI.box 500 20, UI.box 500 20], UI.col [UI.spacer, UI.box 10 10, UI.spacer 2]]
  let mut allOk := true
  for w in widgets do
    for (mw, mh) in [(0, 0), (10, 5), (100, 50), (320, 240), (1000, 800)] do
      for (nw, nh) in [(0, 0), (mw / 2, mh / 2), (mw, mh)] do
        let c : Constraints := ⟨Min.min nw mw, mw, Min.min nh mh, mh, Nat.min_le_right _ _, Nat.min_le_right _ _⟩
        let r := layout w c
        -- every node lies within the root
        let inside := (r.node.rects 0 0).all fun (x, y, cw, ch) =>
          x + cw ≤ r.size.w && y + ch ≤ r.size.h
        if !(decide (c.Admits r.size)) || !inside then allOk := false
  let t2 ← check "layout sweep: sizes admitted, all nodes inside root" allOk
  let flex := layout (UI.row (Msg := Unit) [UI.spacer, UI.box 40 10, UI.spacer 3] (gap := 0)) (Constraints.tight ⟨200, 10⟩)
  let t3 ← check "flex: spacers share free space 1:3"
    ((flex.node.rects 0 0).map (·.1) == [0, 0, 40, 80])
  return t1 && t2 && t3

def appTests : IO Bool := do
  let rt := counterAfterClicks
  let t1 ← check "counter: 4 taps up, 1 down, '+' key → 4" (rt.model.count == 4)
  let t2 ← check "counter: history recorded" (rt.model.history == [0, 1, 2, 3, 2, 3, 4])
  -- press on "+" but release outside: no tap
  let rt0 := Runtime.start Examples.Counter.app 480 360
  let ev := match rt0.targets.toList.find? (fun t => t.tapMsg?.any (· == Examples.Counter.Msg.inc)) with
    | some t => [Event.pointerDown (t.x + 2).toF (t.y + 2).toF .left, .pointerUp 1 1 .left]
    | none => []
  let t3 ← check "press then release elsewhere does not dispatch" ((rt0.simulate ev).model.count == 0)
  let t4 ← check "three tap targets found" (rt0.targets.size == 3)
  return t1 && t2 && t3 && t4

def codecTests : IO Bool := do
  let fb := Raster.render 37 23 Examples.primitives (Color.hex 0x123456)
  let ok := match Image.decodePNG (Image.toPNG fb) with
    | .ok (w, h, d) => w == 37 && h == 23 && d == fb.data
    | .error _ => false
  check "PNG round-trip (odd size, all filters)" ok

def main (args : List String) : IO UInt32 := do
  let update := args.contains "--update"
  IO.println "golden images:"
  let mut ok := true
  for g in goldens do
    ok := (← checkGolden update g) && ok
  IO.println "layout:"
  ok := (← layoutTests) && ok
  IO.println "app runtime:"
  ok := (← appTests) && ok
  IO.println "codecs:"
  ok := (← codecTests) && ok
  ok := (← Tests.PngDecode.run) && ok
  IO.println "tiles / bare-metal:"
  ok := (← Tests.Tile.run) && ok
  IO.println "partial redraw:"
  ok := (← Tests.Damage.run) && ok
  IO.println "stateful controls:"
  ok := (← Tests.Controls.run) && ok
  IO.println "TrueType text:"
  ok := (← Tests.Text.run) && ok
  IO.println "camera and gestures:"
  ok := (← Tests.Camera.run) && ok
  IO.println "GPU pipeline (interpreted):"
  ok := (← Tests.GPU.run) && ok
  IO.println (if ok then "ALL TESTS PASSED" else "SOME TESTS FAILED")
  return if ok then 0 else 1
