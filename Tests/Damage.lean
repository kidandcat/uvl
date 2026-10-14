import Examples.Scenes
import Examples.Counter

/-!
Partial redraw checks: after any sequence of events, the incrementally updated
frame (`Runtime.present`) must be bit-identical to a full render, and small
changes (hovering a button) must only repaint a small part of the frame.
-/

namespace Tests.Damage
open UVL

def check (name : String) (cond : Bool) : IO Bool := do
  IO.println s!"  [{if cond then "ok" else "FAIL"}] {name}"
  return cond

def fullFrame {Model Msg : Type} (rt : Runtime Model Msg) : ByteArray :=
  (Raster.render rt.width rt.height (rt.tree.2.toOps 0 0 rt.pointerState) rt.app.background).data

def centre {Msg : Type} (t : Layout.Target Msg) : Float × Float :=
  ((t.x + t.w / 2).toF, (t.y + t.h / 2).toF)

/-- A session over the counter app: hover, leave, press, release, keys. -/
def counterEvents (rt : Runtime Examples.Counter.Model Examples.Counter.Msg) : List Event :=
  let at_ (i : Nat) := match rt.targets[i]? with
    | some t => centre t
    | none => (0, 0)
  let (ax, ay) := at_ 0; let (bx, by_) := at_ 1; let (cx, cy) := at_ 2
  [.pointerMove ax ay, .pointerMove (ax + 1) ay, .pointerMove bx by_, .pointerLeave,
   .pointerMove ax ay, .pointerDown ax ay .left, .pointerUp ax ay .left,
   .pointerDown bx by_ .left, .pointerMove cx cy, .pointerUp cx cy .left,
   .keyDown (.char '+'), .keyDown (.char '+'), .keyDown (.char '-'),
   .pointerMove 1 1, .resize 400 300, .pointerMove cx cy, .pointerDown cx cy .left,
   .pointerUp cx cy .left]

def run : IO Bool := do
  let rt0 := (Runtime.start Examples.Counter.app 480 360).present
  let mut rt := rt0
  let mut identical := true
  let mut hoverArea := 0
  let mut presents := 0
  for e in counterEvents rt0 do
    rt := rt.handle e
    if rt.dirty then
      rt := rt.present
      presents := presents + 1
      identical := identical && rt.pixels == fullFrame rt
      if let .pointerMove .. := e then
        if presents == 1 then hoverArea := rt.damage.foldl (· + ·.area) 0
  let t1 ← check s!"counter: {presents} incremental frames identical to full renders" identical
  let t2 ← check s!"counter: hovering a button repaints {hoverArea} of {480 * 360} px"
    (0 < hoverArea && hoverArea * 10 < 480 * 360)
  -- scene edits: move one op, insert one op, remove one op
  let ops := Examples.primitives
  let f0 := Frame.full 480 320 ops Color.white
  let moved := ops.set! 2 (.translate 7 5 #[ops[2]!])
  let edits : List (String × Array RenderOp) :=
    [("move", moved), ("insert", ops.insertIdx! 3 (.circle ⟨100, 100⟩ 20 Color.black)),
     ("remove", ops.eraseIdx! 1), ("same", ops)]
  let mut allSame := true
  for (name, ops') in edits do
    let (f, ws) := f0.update 480 320 ops' Color.white
    let same := f.data == (Raster.render 480 320 ops' Color.white).data
    unless same do IO.println s!"    {name}: differs ({ws.size} windows)"
    allSame := allSame && same
  let t3 ← check "scene edits (move/insert/remove/none) match full renders" allSame
  let t4 ← check "unchanged scene has no damage" ((damage 480 320 ops ops).isEmpty)
  return t1 && t2 && t3 && t4

end Tests.Damage
