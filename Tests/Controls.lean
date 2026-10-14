import Examples.Controls

/-!
Stateful controls driven by scripted events: dragging a slider (pointer
capture), toggling checkboxes, typing in a text field (focus, editing keys,
Enter, Escape) and scrolling a list (wheel routing, clamping, taps on the
scrolled content).
-/

namespace Tests.Controls
open UVL Examples.Controls

def check (name : String) (cond : Bool) : IO Bool := do
  IO.println s!"  [{if cond then "ok" else "FAIL"}] {name}"
  return cond

abbrev RT := Runtime Model Msg

def find (rt : RT) (p : Layout.Target Msg → Bool) : Option (Layout.Target Msg) :=
  rt.targets.find? p

def isDrag (t : Layout.Target Msg) : Bool := match t.action with | .drag _ => true | _ => false
def isScroll (t : Layout.Target Msg) : Bool := match t.action with | .scroll .. => true | _ => false
def isInput (t : Layout.Target Msg) : Bool := match t.action with | .input .. => true | _ => false

def start : RT := Runtime.start app 720 360

/-- The session that also produces the `controls` golden image. -/
def session : RT := Id.run do
  let mut rt := start
  if let some t := find rt isScroll then
    rt := rt.simulate [.pointerMove (t.x + 50).toF (t.y + 50).toF, .scroll 0 95]
  if let some t := rt.targets[6]? then
    rt := rt.simulate (Runtime.click (t.x + 50).toF (t.y + t.h / 2).toF)
  if let some t := find rt isDrag then
    let y := (t.y + t.h / 2).toF
    rt := rt.simulate [.pointerMove (t.x.toF + 20) y, .pointerDown (t.x.toF + 20) y .left,
      .pointerMove (t.x.toF + 140) y, .pointerUp (t.x.toF + 140) y .left]
  if let some t := find rt isInput then
    let (x, y) := ((t.x + 20).toF, (t.y + t.h / 2).toF)
    rt := rt.simulate (Runtime.click x y ++ [.textInput "L", .textInput "e", .textInput "a",
      .textInput "n", .textInput " ", .textInput "4"])
  return rt

def run : IO Bool := do
  let mut ok := true
  -- slider: press and drag, captured even outside the track, clamped
  let rt := start
  let some s := find rt isDrag | check "slider target" false
  let y := (s.y + s.h / 2).toF
  let x0 := s.x.toF + 10
  let x1 := (s.x + s.w).toF - 10
  let a := rt.simulate [.pointerMove (x0 + 40) y, .pointerDown (x0 + 40) y .left]
  ok := (← check s!"slider: press sets the value under the pointer ({a.model.volume})"
    ((a.model.volume - 40 / (x1 - x0)).abs < 1.0e-9)) && ok
  let b := a.simulate [.pointerMove (x1 + 300) (y + 200)]
  ok := (← check "slider: drag outside the track is captured and clamped to 1"
    (b.model.volume == 1 && b.captured.isSome && !b.pointerState.overlay)) && ok
  let c := b.simulate [.pointerUp (x1 + 300) (y + 200) .left, .pointerMove (x0 + 10) y]
  ok := (← check "slider: release ends the capture" (c.model.volume == 1 && c.captured.isNone)) && ok
  -- checkboxes
  let taps := rt.targets.filter fun t => (t.tapMsg?.map fun | .toggle _ => true | _ => false).getD false
  let rt2 := match taps[1]? with
    | some t => rt.simulate (Runtime.click (t.x + 5).toF (t.y + 5).toF)
    | none => rt
  ok := (← check "checkbox: tap toggles" (rt2.model.options == #[true, true])) && ok
  -- text field
  let some f := find rt isInput | check "text field target" false
  let (fx, fy) := ((f.x + 20).toF, (f.y + f.h / 2).toF)
  let t1 := rt.simulate (Runtime.click fx fy ++ [.textInput "A", .textInput "d", .textInput "x",
    .keyDown .backspace, .textInput "a", .keyDown .home, .textInput ">", .keyDown .end_,
    .keyDown .left, .keyDown .delete, .textInput "!"])
  ok := (← check s!"text field: focus, typing and editing keys → \"{t1.model.name.text}\""
    (t1.model.name.text == ">Ad!" && t1.model.name.focused && t1.focus.isSome)) && ok
  let t2 := t1.simulate [.keyDown .enter, .keyDown (.char 'r')]
  ok := (← check "text field: Enter submits; keys go to the field only"
    (t2.model.greeted == ">Ad!" && t2.model.name.text == ">Ad!")) && ok
  let t3 := t2.simulate [.keyDown .escape]
  ok := (← check "text field: Escape blurs" (!t3.model.name.focused && t3.focus.isNone)) && ok
  let t4 := t1.simulate (Runtime.click 5 5)
  ok := (← check "text field: clicking elsewhere blurs" (!t4.model.name.focused && t4.focus.isNone)) && ok
  let t5 := t1.simulate (Runtime.click (f.x + 2).toF fy)
  ok := (← check "text field: a click places the cursor" (t5.model.name.cursor == 0)) && ok
  -- scroll view
  let some sv := find rt isScroll | check "scroll target" false
  let (sx, sy) := ((sv.x + 50).toF, (sv.y + 50).toF)
  let r1 := rt.simulate [.pointerMove sx sy, .scroll 0 100]
  ok := (← check s!"scroll: the wheel moves the list ({r1.model.scroll} px)" (r1.model.scroll == 100)) && ok
  let r2 := r1.simulate [.scroll 0 100000]
  let maxOff := match find r2 isScroll with
    | some { action := .scroll _ m _, .. } => m
    | _ => 0
  ok := (← check s!"scroll: clamped to the content ({r2.model.scroll} = {maxOff})"
    (r2.model.scroll == maxOff && maxOff > 0)) && ok
  let r3 := r1.simulate (Runtime.click sx (sv.y + 5).toF)
  -- rows are 29 px + 2 px gap: at offset 100, y = 5 is row 3 (93..122)
  ok := (← check s!"scroll: a tap hits the scrolled row ({r3.model.picked})"
    (r3.model.picked.any (· == 3))) && ok
  let outside := r1.simulate [.pointerMove 5 5, .scroll 0 50]
  ok := (← check "scroll: the wheel outside the list does nothing" (outside.model.scroll == 100)) && ok
  -- hidden rows are not targets
  ok := (← check "scroll: only visible rows are targets"
    (r1.targets.all fun t => t.y + t.h ≤ sv.y + sv.h || t.x < sv.x)) && ok
  -- partial redraw stays exact through drags, typing and scrolling
  let script : List Event := [.pointerMove (x0 + 40) y, .pointerDown (x0 + 40) y .left,
    .pointerMove (x0 + 90) y, .pointerUp (x0 + 90) y .left] ++ Runtime.click fx fy ++
    [.textInput "h", .textInput "i", .keyDown .left, .pointerMove sx sy, .scroll 0 37,
     .scroll 0 50, .pointerMove sx (sy + 40)] ++ Runtime.click sx (sy + 40)
  let mut rp := start.present
  let mut same := true
  for e in script do
    rp := (rp.handle e).present
    same := same && rp.pixels == rp.frame
  ok := (← check s!"partial redraw: {script.length} interaction frames identical to full renders" same) && ok
  return ok

end Tests.Controls
