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

def start : RT := Runtime.start app 960 360

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
  -- the level meter settles; the caret is in the "on" half of its blink
  return rt.simulate [.tick 0.5]

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
  -- the level meter tweens towards the volume
  let m0 := c.model.meter
  let m1 := (c.simulate [.tick 0.1]).model.meter
  let settled := c.simulate [.tick 0.1, .tick 0.1, .tick 0.1, .tick 0.15]
  ok := (← check s!"tween: the meter eases to the volume ({m0.value} → {m1.value} → {settled.model.meter.value})"
    (c.animating && m0.value < m1.value && m1.value < 1 && settled.model.meter.value == 1 &&
      !settled.animating)) && ok
  let easings := [Easing.linear, .inQuad, .outQuad, .inOutQuad, .inCubic, .outCubic, .inOutCubic,
    .outBack, .outElastic]
  ok := (← check "easing: every curve maps 0 to 0 and 1 to 1"
    (easings.all fun e => (e.apply 0).abs < 1.0e-9 && (e.apply 1 - 1).abs < 1.0e-9)) && ok
  ok := (← check "easing: outBack overshoots, outCubic does not"
    (Easing.outBack.apply 0.7 > 1 && Easing.outCubic.apply 0.7 < 1)) && ok
  let tw := (Tween.at 0 1 .linear).to 1 |>.step 0.5
  let tw2 := tw.to 0
  ok := (← check "tween: retargeting starts from the current value"
    ((tw.value - 0.5).abs < 1.0e-9 && (tw2.value - 0.5).abs < 1.0e-9 &&
      ((tw2.step 1).value).abs < 1.0e-9)) && ok
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
  -- caret blink and hover fade (runtime clock)
  let b0 := rt.simulate (Runtime.click fx fy)
  let b1 := b0.simulate [.tick 0.3]
  let b2 := b1.simulate [.tick 0.3]
  ok := (← check "caret: blinks off after half a period, frame changes"
    (b0.blinkOn && b1.blinkOn && !b2.blinkOn && b2.dirty && b0.animating &&
      b1.frame == b0.frame && b2.frame != b1.frame)) && ok
  let b3 := b2.simulate [.textInput "z"]
  ok := (← check "caret: typing restarts the blink" (b3.blinkOn && b3.model.name.text == "z")) && ok
  ok := (← check "caret: nothing animates without focus" (!rt.animating)) && ok
  let some cb := taps[0]? | check "checkbox target" false
  let h0 := rt.simulate [.pointerMove (cb.x + 5).toF (cb.y + 5).toF]
  let h1 := h0.simulate [.tick 0.06]
  let h2 := h1.simulate [.tick 0.1]
  ok := (← check s!"hover: feedback fades in ({h0.hoverFade} → {h1.hoverFade} → {h2.hoverFade})"
    (h0.hoverFade == 0 && h0.animating && h1.hoverFade > 0.4 && h1.hoverFade < 0.6 &&
      h2.hoverFade == 1 && !h2.animating && h1.frame != h0.frame && h2.frame != h1.frame)) && ok
  -- selection and clipboard
  let typed := rt.simulate (Runtime.click fx fy ++ [.textInput "hello world"])
  let s1 := typed.simulate [.keyDown .shift, .keyDown .left, .keyDown .left, .keyDown .left,
    .keyDown .left, .keyDown .left, .keyUp .shift]
  ok := (← check s!"selection: Shift+Left extends (\"{s1.model.name.selectedText}\")"
    (s1.model.name.selectedText == "world" && s1.model.name.cursor == 6)) && ok
  let s2 := s1.simulate [.keyDown .ctrl, .keyDown (.char 'c'), .keyUp .ctrl]
  ok := (← check "clipboard: Ctrl+C copies the selection"
    (s2.clipboard.any (· == "world") && s2.model.name.text == "hello world")) && ok
  let (copied, s2') := s2.takeClipboard
  ok := (← check "clipboard: the shell takes the text once"
    (copied.any (· == "world") && s2'.clipboard.isNone)) && ok
  let s3 := s2'.simulate [.keyDown .ctrl, .keyDown (.char 'x'), .keyUp .ctrl]
  ok := (← check s!"clipboard: Ctrl+X cuts (\"{s3.model.name.text}\")"
    (s3.clipboard.any (· == "world") && s3.model.name.text == "hello " &&
      s3.model.name.selection?.isNone)) && ok
  let s4 := s3.simulate [.keyDown .home, .textInput "say "]
  ok := (← check s!"clipboard: pasted text is inserted as one edit (\"{s4.model.name.text}\")"
    (s4.model.name.text == "say hello " && s4.model.name.cursor == 4)) && ok
  let s5 := s4.simulate [.keyDown .ctrl, .keyDown (.char 'a'), .keyUp .ctrl, .textInput "X"]
  ok := (← check "selection: Ctrl+A then typing replaces everything" (s5.model.name.text == "X")) && ok
  let s6 := s1.simulate [.keyDown .right]
  ok := (← check "selection: Right collapses to the end"
    (s6.model.name.selection?.isNone && s6.model.name.cursor == 11)) && ok
  let s7 := s1.simulate [.keyDown .backspace]
  ok := (← check "selection: Backspace deletes it" (s7.model.name.text == "hello ")) && ok
  let some f' := find typed isInput | check "text field target" false
  let x0' := (f'.x + 10).toF
  let d1 := typed.simulate [.pointerMove x0' fy, .pointerDown x0' fy .left,
    .pointerMove (x0' + 30) fy, .pointerMove (x0' + 1000) fy, .pointerUp (x0' + 1000) fy .left]
  ok := (← check s!"selection: dragging selects (\"{d1.model.name.selectedText}\")"
    (d1.model.name.selectedText == "hello world")) && ok
  let d2 := typed.simulate ([.keyDown .home] ++ [.keyDown .shift] ++
    Runtime.click (f'.x + f'.w - 12).toF fy ++ [.keyUp .shift])
  ok := (← check "selection: Shift+click extends" (d2.model.name.selectedText == "hello world")) && ok
  let d3 := s1.simulate (Runtime.click 5 5)
  ok := (← check "selection: blur clears it" (d3.model.name.selection?.isNone)) && ok
  -- word navigation and double-click
  let w0 := typed
  let w1 := w0.simulate [.keyDown .ctrl, .keyDown .left]
  let w2 := w1.simulate [.keyDown .left]
  let w3 := w2.simulate [.keyDown .right]
  let w4 := w3.simulate [.keyDown .shift, .keyDown .right, .keyUp .shift, .keyUp .ctrl]
  ok := (← check s!"words: Ctrl+Left/Right ({w1.model.name.cursor}, {w2.model.name.cursor}, {w3.model.name.cursor}), Ctrl+Shift+Right selects (\"{w4.model.name.selectedText}\")"
    (w1.model.name.cursor == 6 && w2.model.name.cursor == 0 && w3.model.name.cursor == 5 &&
      w4.model.name.selectedText == " world")) && ok
  let w5 := w0.simulate [.keyDown .ctrl, .keyDown .backspace, .keyUp .ctrl]
  ok := (← check s!"words: Ctrl+Backspace deletes a word (\"{w5.model.name.text}\")"
    (w5.model.name.text == "hello ")) && ok
  -- "world" starts about 48 px into the text, after the 8 px padding
  let wx := (f'.x + 8 + 60).toF
  let dc := w0.simulate (Runtime.click wx fy ++ [.tick 0.1] ++ Runtime.click wx fy)
  ok := (← check s!"words: double-click selects the word (\"{dc.model.name.selectedText}\")"
    (dc.model.name.selectedText == "world")) && ok
  let slow := w0.simulate (Runtime.click wx fy ++ [.tick 0.6] ++ Runtime.click wx fy)
  ok := (← check "words: two slow clicks are not a double-click" (slow.model.name.selection?.isNone)) && ok
  -- text area
  let inputs := rt.targets.filter isInput
  let some ta := inputs[1]? | check "text area target" false
  let a0 := rt.simulate (Runtime.click (ta.x + 20).toF (ta.y + 14).toF)
  let lay := UI.TextLayout.make (Text.uvlSans ()) 15 a0.model.notes.text (wrap := true)
    (maxWidth := ta.w.toFloat - 16)
  ok := (← check s!"text area: wraps into {lay.lines.size} lines within the width"
    (a0.model.notes.focused && lay.lines.size ≥ 4 && (List.range lay.lines.size).all fun k =>
      (lay.stops[k]!.back!) ≤ ta.w.toFloat - 16 + 15 * 0.3)) && ok
  let a1 := a0.simulate [.keyDown .ctrl, .keyDown .end_, .keyUp .ctrl]
  let a2 := a1.simulate [.keyDown .up]
  ok := (← check "text area: Ctrl+End, then Up moves one line up"
    (a1.model.notes.cursor == a1.model.notes.text.length &&
      lay.lineOf a2.model.notes.cursor + 1 == lay.lineOf a1.model.notes.cursor)) && ok
  let a3 := a1.simulate [.keyDown .enter, .textInput "one", .keyDown .enter, .textInput "two",
    .keyDown .enter, .textInput "three", .keyDown .enter, .textInput "four", .keyDown .enter,
    .textInput "five", .keyDown .enter, .textInput "six"]
  ok := (← check s!"text area: Enter breaks lines and the view scrolls to the cursor ({a3.model.notes.scroll} px)"
    (a3.model.notes.text.endsWith "\none\ntwo\nthree\nfour\nfive\nsix" && a3.model.notes.scroll > 0)) && ok
  let a4 := a3.simulate [.keyDown .ctrl, .keyDown .home, .keyUp .ctrl]
  ok := (← check "text area: Ctrl+Home scrolls back to the top"
    (a4.model.notes.cursor == 0 && a4.model.notes.scroll == 0)) && ok
  let a5 := a3.simulate [.keyDown .home, .keyDown .shift, .keyDown .up, .keyUp .shift]
  let w1' := a3.simulate [.pointerMove (ta.x + 40).toF (ta.y + 40).toF, .scroll 0 (-100)]
  let w2' := w1'.simulate [.scroll 0 15]
  ok := (← check s!"text area: the wheel scrolls it ({a3.model.notes.scroll} → {w1'.model.notes.scroll} → {w2'.model.notes.scroll})"
    (w1'.model.notes.scroll == 0 && (w2'.model.notes.scroll - 15).abs < 1.0e-9 &&
      w2'.model.scroll == 0)) && ok
  ok := (← check s!"text area: Shift+Up selects across lines (\"{a5.model.notes.selectedText}\")"
    (a5.model.notes.selectedText == "five\n")) && ok
  -- undo / redo
  let u0 := rt.simulate (Runtime.click fx fy ++ [.textInput "a", .textInput "b", .textInput "c",
    .keyDown .left, .keyDown .left, .textInput "X", .keyDown .end_, .keyDown .backspace,
    .keyDown .backspace])
  let undo := [Event.keyDown .ctrl, .keyDown (.char 'z'), .keyUp .ctrl]
  let u1 := u0.simulate undo
  let u2 := u1.simulate undo
  let u3 := u2.simulate undo
  let u4 := u3.simulate [.keyDown .ctrl, .keyDown (.char 'y'), .keyUp .ctrl]
  let u5 := u4.simulate [.keyDown .ctrl, .keyDown .shift, .keyDown (.char 'z'), .keyUp .shift, .keyUp .ctrl]
  ok := (← check s!"undo: keystroke runs undo as one step (\"{u0.model.name.text}\" ← \"{u1.model.name.text}\" ← \"{u2.model.name.text}\" ← \"{u3.model.name.text}\")"
    (u0.model.name.text == "aX" && u1.model.name.text == "aXbc" && u2.model.name.text == "abc" &&
      u3.model.name.text == "")) && ok
  ok := (← check "undo: Ctrl+Y and Ctrl+Shift+Z redo"
    (u4.model.name.text == "abc" && u5.model.name.text == "aXbc")) && ok
  let u6 := u2.simulate [.textInput "!"]
  ok := (← check "undo: a new edit clears the redo history"
    (u6.model.name.redo.isEmpty && (u6.simulate undo).model.name.text == "abc")) && ok
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
    [.textInput "h", .textInput "i", .keyDown .left, .tick 0.6, .keyDown .shift, .keyDown .home,
     .keyUp .shift, .tick 0.6, .textInput "o", .pointerMove sx sy, .tick 0.05, .scroll 0 37,
     .pointerMove (ta.x + 20).toF (ta.y + 14).toF, .pointerDown (ta.x + 20).toF (ta.y + 14).toF .left,
     .pointerMove (ta.x + 90).toF (ta.y + 60).toF, .pointerUp (ta.x + 90).toF (ta.y + 60).toF .left,
     .keyDown .ctrl, .keyDown .end_, .keyUp .ctrl, .keyDown .enter, .textInput "a", .keyDown .enter,
     .textInput "b", .keyDown .enter, .textInput "c", .keyDown .up,
     .scroll 0 50, .pointerMove sx (sy + 40)] ++ Runtime.click sx (sy + 40)
  let mut rp := start.present
  let mut same := true
  for e in script do
    rp := (rp.handle e).present
    same := same && rp.pixels == rp.frame
  ok := (← check s!"partial redraw: {script.length} interaction frames identical to full renders" same) && ok
  return ok

end Tests.Controls
