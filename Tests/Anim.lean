import Examples.Anim

/-!
Headless checks for the verified animation demo.

The theorems in `UVL.Anim` are checked by the compiler (no `sorry`). These tests
check that the widget tree and the rasterizer consume that result: the laid-out
rectangle is the proved pixel, the painted center matches, and interruption,
cancel, grouping and unequal frame steps agree.
-/

namespace Tests.Anim

open UVL UVL.Anim Examples.Anim

def check (name : String) (cond : Bool) : IO Bool := do
  IO.println s!"  [{if cond then "ok" else "FAIL"}] {name}"
  return cond

def rects (m : Model) : List (Nat × Nat × Nat × Nat) :=
  let r := Layout.layout (view m) (Layout.Constraints.tight ⟨stageW, stageH⟩)
  r.node.rects 0 0

def findSize (m : Model) (w h : Nat) : List (Nat × Nat) :=
  (rects m).filterMap fun (x, y, rw, rh) => if rw = w && rh = h then some (x, y) else none

def pixel (m : Model) (x y : Nat) : RGBA8 :=
  let fb := renderAt m
  if hx : x < stageW then
    if hy : y < stageH then fb.getPixel ⟨x, hx⟩ ⟨y, hy⟩ else default
  else default

def inside (rs : List (Nat × Nat × Nat × Nat)) : Bool :=
  rs.all fun (x, y, w, h) => x + w ≤ stageW && y + h ≤ stageH

def run : IO Bool := do
  let mut ok := true
  let start := atMs 0
  let mid := atMs 400
  let done := atMs 800
  ok := (← check "endpoint: t = 0 is the start pixel and alpha 0"
    (motionPixel start == 24 && fadeByte start == 0)) && ok
  ok := (← check "endpoint: t = 800 ms is the target pixel and alpha 255"
    (motionPixel done == 280 && fadeByte done == 255)) && ok
  ok := (← check "sync: sequence and stagger share the 4/5 s duration"
    (decide (sumDur [leg 24 120, leg 120 200, leg 200 280] = 4 / 5) &&
      decide (staggerDuration (1 / 5) (2 / 5) 3 = 4 / 5) &&
      spanPixel route0[0]! (4 / 5) == 120 && spanPixel route0[2]! (4 / 5) == 280 &&
      spanPixel route0[0]! (4 / 15) == 120 && spanPixel route0[1]! (4 / 15) == 120 &&
      (done.bars.map (spanPixel · (groupElapsed done))) == [36, 36, 36])) && ok
  let steps := [100, 150, 50, 500].foldl (fun m dt => update (.advance dt) m) {}
  ok := (← check "frame independence: 100+150+50+500 ms equals one 800 ms jump"
    (motionPixel steps == motionPixel done && fadeByte steps == fadeByte done &&
      steps.ms == done.ms)) && ok
  let midPx := motionPixel mid
  ok := (← check s!"monotone: mid pixel {midPx} is strictly between 24 and 280"
    (24 < midPx && midPx < 280)) && ok
  let retargeted := update (.advance 800) (update .retarget mid)
  ok := (← check "retarget: after another 800 ms the pixel is 100"
    (motionPixel retargeted == 100)) && ok
  ok := (← check "reverse: motion and bars return to their starts"
    (motionPixel reversed == 24 &&
      (reversed.bars.map (spanPixel · (groupElapsed reversed))) == [8, 8, 8])) && ok
  let snapped := update .snap mid
  let snappedLater := update (.advance 500) snapped
  ok := (← check "cancel snap: the pixel is the target immediately and stays there"
    (motionPixel snapped == 280 && motionPixel snappedLater == 280)) && ok
  let held := update .hold mid
  let heldLater := update (.advance 900) held
  ok := (← check "cancel hold: the pixel is the mid sample and does not move"
    (motionPixel held == midPx && motionPixel heldLater == midPx)) && ok
  -- layout consumes the integer pixel
  let motionAt := findSize done 37 29
  let fadeAt := findSize done 41 41
  ok := (← check s!"layout: motion box is at the proved pixel {motionAt}"
    (motionAt == [(280, 48)])) && ok
  ok := (← check s!"layout: fade box stays put {fadeAt}" (fadeAt == [(24, 96)])) && ok
  ok := (← check "layout: every node is inside the stage"
    (inside (rects start) && inside (rects mid) && inside (rects done) && inside (rects reversed))) && ok
  let bg := (Color.hex 0xF5F7FA).toRGBA8
  let blue := Color.blue.toRGBA8
  let red := Color.red.toRGBA8
  ok := (← check "raster: settled motion center is the target blue"
    (pixel done (280 + 12) (48 + 12) == blue)) && ok
  ok := (← check "raster: start motion center is blue, the old slot is background"
    (pixel start (24 + 12) (48 + 12) == blue && pixel start (280 + 12) (48 + 12) == bg)) && ok
  ok := (← check "raster: fade is background at t = 0 and red at the end"
    (pixel start (24 + 20) (96 + 20) == bg && pixel done (24 + 20) (96 + 20) == red)) && ok
  -- runtime clock, unequal frames
  let rt1 := (Runtime.start app stageW stageH).simulate [.tick 1]
  let rt2 := (Runtime.start app stageW stageH).simulate [.tick 0.25, .tick 0.75]
  ok := (← check "runtime: 1.0 s and 0.25+0.75 s land on the same pixel"
    (rt1.model.ms == 1000 && rt2.model.ms == 1000 &&
      motionPixel rt1.model == 280 && motionPixel rt2.model == 280)) && ok
  let clicked := Id.run do
    let rt := (Runtime.start app stageW stageH).simulate [.tick 0.4]
    let hit := rt.targets.find? fun t => t.tapMsg? == some .reverse
    match hit with
    | some t => (rt.simulate (Runtime.click (t.x + t.w / 2).toF (t.y + t.h / 2).toF)).simulate [.tick 0.8]
    | none => rt
  ok := (← check "runtime: clicking Reverse mid-flight returns the motion to 24"
    (clicked.model.note == "reverse" && motionPixel clicked.model == 24)) && ok
  return ok

end Tests.Anim
