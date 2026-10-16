import UVL.App.Event
import UVL.UI.Basic
import UVL.Output.Image
import UVL.Render.Damage

/-!
# Elm-style application runtime

An application is `init`, a pure `update : Msg → Model → Model` and a pure
`view : Model → Widget Msg`. The runtime owns everything else: layout, hit
testing, hover/press feedback, pointer capture while dragging, keyboard focus,
routing wheel events to scroll views, and deciding when a new frame is needed.

Widget state (a slider's value, a text field's contents and cursor, a scroll
offset) lives in the model, Elm style: widgets dispatch messages carrying the
new state. Only the focused input's id and the captured drag target live here.

The runtime is itself pure (`Runtime.handle : Runtime → Event → Runtime`), so
platform shells are thin loops and interactions can be tested headlessly by
feeding scripted events (`Runtime.simulate`).
-/

namespace UVL

open Layout

structure App (Model Msg : Type) where
  init : Model
  update : Msg → Model → Model
  view : Model → UI.Widget Msg
  /-- Map events that no widget handles (keys, ticks, …) to messages. -/
  subscriptions : Event → Model → Option Msg := fun _ _ => none
  /-- Whether the app currently wants `tick` events (animations). -/
  animating : Model → Bool := fun _ => false
  background : Color := Color.white
  title : String := "uvl"

structure Runtime (Model Msg : Type) where
  app : App Model Msg
  model : Model
  width : Nat
  height : Nat
  /-- Laid-out tree of the current view. -/
  tree : (s : Size) × Placed Msg s
  targets : Array (Target Msg)
  pointer : Option (Nat × Nat) := none
  /-- Target index under the pointer when the button went down. -/
  pressed : Option Nat := none
  hovered : Option Nat := none
  /-- The drag target that owns the pointer until the button is released. -/
  captured : Option (Target Msg) := none
  /-- Id of the input that receives keyboard events. -/
  focus : Option String := none
  /-- Seconds of `tick`s received. -/
  time : Float := 0
  /-- `time` of the last event delivered to an input (restarts the caret blink). -/
  inputTime : Float := 0
  /-- Progress `0..1` of the hover feedback of the hovered target fading in. -/
  hoverFade : Float := 1
  /-- `time` and position of the last press on an input (double-click detection). -/
  lastPress : Option (Float × Float × Float) := none
  /-- Modifier keys held down. -/
  shift : Bool := false
  ctrl : Bool := false
  /-- Text copied (Ctrl+C / Ctrl+X) that the shell should put on the system
  clipboard, then clear with `takeClipboard`. Pasting needs no runtime support:
  shells deliver the pasted text as `textInput`. -/
  clipboard : Option String := none
  /-- A new frame must be presented. -/
  dirty : Bool := true
  quit : Bool := false
  /-- The last presented frame, reused by `present` for partial redraws. -/
  presented : Option Frame := none
  /-- Windows that changed in the last `present` (what a shell must upload). -/
  damage : Array Window := #[]

namespace Runtime

variable {Model Msg : Type}

def layoutView (app : App Model Msg) (model : Model) (w h : Nat) :
    ((s : Size) × Placed Msg s) × Array (Target Msg) :=
  let r := layout (app.view model) (Constraints.tight ⟨w, h⟩)
  (⟨r.size, r.node⟩, (r.node.targets 0 0).toArray)

def start (app : App Model Msg) (w h : Nat) : Runtime Model Msg :=
  let (tree, targets) := layoutView app app.init w h
  { app, model := app.init, width := w, height := h, tree, targets }

def relayout (rt : Runtime Model Msg) : Runtime Model Msg :=
  let (tree, targets) := layoutView rt.app rt.model rt.width rt.height
  let hovered := rt.pointer.bind fun (x, y) => pressIndex targets x y
  { rt with tree, targets, hovered, dirty := true }

def dispatch (rt : Runtime Model Msg) (msg : Msg) : Runtime Model Msg :=
  { rt with model := rt.app.update msg rt.model }.relayout

def dispatchOpt (rt : Runtime Model Msg) : Option Msg → Runtime Model Msg
  | some m => rt.dispatch m
  | none => rt

def dispatchIf (rt : Runtime Model Msg) (i : Nat) : Runtime Model Msg :=
  match rt.targets[i]? >>= Target.tapMsg? with
  | some m => rt.dispatch m
  | none => rt

/-- Equality of optional target indices. Written out instead of `==` so the
compiler does not reuse a specialization that lives in the `Lean` package,
which standalone (WebAssembly) builds do not link. -/
def sameTarget : Option Nat → Option Nat → Bool
  | some a, some b => a == b
  | none, none => true
  | _, _ => false

def sameId : Option String → Option String → Bool
  | some a, some b => a == b
  | none, none => true
  | _, _ => false

@[inline] def toPx (v : Float) : Nat := if v <= 0 then 0 else v.floor.toUInt64.toNat

/-- A pointer event in `t`'s coordinates. -/
def localInfo (t : Target Msg) (phase : DragPhase) (x y : Float) : PointerInfo :=
  { phase, x := x - t.ox, y := y - t.oy, w := t.fw.toF, h := t.fh.toF }

/-- Ids of the input targets, in paint order. -/
def inputIds (rt : Runtime Model Msg) : Array String :=
  rt.targets.filterMap Target.inputId?

/-- Deliver an event to the input `id` (if it is in the view). -/
def sendInput (rt : Runtime Model Msg) (id : String) (ev : InputEvent) : Runtime Model Msg :=
  let rt := { rt with inputTime := rt.time, dirty := true }
  match rt.targets.find? (fun t => sameId t.inputId? (some id)) with
  | some { action := .input _ f _, .. } => rt.dispatchOpt (f ev)
  | _ => rt

/-- The focused input's target. -/
def focusedTarget (rt : Runtime Model Msg) : Option (Target Msg) :=
  rt.focus >>= fun id => rt.targets.find? (fun t => sameId t.inputId? (some id))

/-- Copy the focused input's selection to `clipboard`. Returns `none` when
nothing is selected. -/
def copySelection (rt : Runtime Model Msg) : Option (Runtime Model Msg) :=
  match rt.focusedTarget with
  | some { action := .input _ _ sel, .. } =>
    if sel.isEmpty then none else some { rt with clipboard := some sel }
  | _ => none

/-- Bounds of the focused input (where a shell places the input method's
candidate window, or a hidden native text field). -/
def inputRect (rt : Runtime Model Msg) : Option Window :=
  rt.focusedTarget.map fun t => ⟨t.x, t.y, t.w, t.h⟩

/-- The accessibility tree of the current view (see `Layout.Semantics`). -/
def semantics (rt : Runtime Model Msg) : Array SemNode :=
  (rt.tree.2.semantics 0 0).toArray

/-- The pending clipboard text, and the runtime with it cleared. -/
def takeClipboard (rt : Runtime Model Msg) : Option String × Runtime Model Msg :=
  (rt.clipboard, { rt with clipboard := none })

/-- Keys that move the cursor (Shift extends the selection with them). -/
def isMovement : Key → Bool
  | .left | .right | .up | .down | .home | .end_ => true
  | _ => false

/-- A key press for the focused input `id`, with modifiers applied. -/
def keyToInput (rt : Runtime Model Msg) (id : String) (k : Key) : Runtime Model Msg :=
  if rt.ctrl then
    match k with
    | .left | .right | .home | .end_ => rt.sendInput id (.word k rt.shift)
    | .backspace | .delete => rt.sendInput id (.word k false)
    | .char 'a' | .char 'A' => rt.sendInput id .selectAll
    | .char 'z' | .char 'Z' => rt.sendInput id (if rt.shift then .redo else .undo)
    | .char 'y' | .char 'Y' => rt.sendInput id .redo
    | .char 'c' | .char 'C' => (rt.copySelection).getD rt
    | .char 'x' | .char 'X' =>
      match rt.copySelection with
      | some rt => rt.sendInput id .cut
      | none => rt
    | _ => rt
  else if rt.shift && isMovement k then rt.sendInput id (.extend k)
  else rt.sendInput id (.key k)

/-- Longest gap between the presses of a double-click, in seconds. -/
def doubleClickTime : Float := 0.5

/-- Length of the caret blink cycle, in seconds (on for the first half). -/
def blinkPeriod : Float := 1.06

/-- Seconds for hover feedback to fade in. -/
def hoverFadeTime : Float := 0.12

def blinkOn (rt : Runtime Model Msg) : Bool :=
  let c := (rt.time - rt.inputTime) / blinkPeriod
  c - c.floor < 0.5

/-- Whether the runtime needs `tick` events: the app animates, a caret blinks
or hover feedback is fading in. -/
def animating (rt : Runtime Model Msg) : Bool :=
  rt.app.animating rt.model || rt.focus.isSome || rt.hoverFade < 1

/-- Move the keyboard focus, telling the old input (`blur`) and the new one
(`focus`). -/
def setFocus (rt : Runtime Model Msg) (new : Option String) : Runtime Model Msg :=
  if sameId rt.focus new then rt else
  let rt := match rt.focus with
    | some id => rt.sendInput id .blur
    | none => rt
  let rt := { rt with focus := new, dirty := true }
  match new with
  | some id => rt.sendInput id .focus
  | none => rt

/-- The input after (or before) the focused one, cyclically. -/
def nextInput (rt : Runtime Model Msg) (back : Bool) : Option String :=
  let ids := rt.inputIds
  if ids.isEmpty then none else
  let i := (ids.findIdx? fun id => sameId (some id) rt.focus).getD (if back then 0 else ids.size - 1)
  ids[(if back then i + ids.size - 1 else i + 1) % ids.size]?

def handle (rt : Runtime Model Msg) (e : Event) : Runtime Model Msg :=
  let focused := rt.focus.isSome
  let rt := match e with
    | .pointerMove x y =>
      let p := (toPx x, toPx y)
      match rt.captured with
      | some t =>
        let rt := { rt with pointer := some p, dirty := true }
        match t.action with
        | .drag f => rt.dispatchOpt (f (localInfo t .move x y))
        | _ => rt
      | none =>
        let hov := pressIndex rt.targets p.1 p.2
        let changed := !sameTarget hov rt.hovered
        let rt := { rt with pointer := some p, hovered := hov,
                            hoverFade := if changed && hov.isSome then 0 else rt.hoverFade,
                            dirty := rt.dirty || changed || rt.pressed.isSome }
        -- dragging inside the pressed (and focused) input selects text
        match rt.pressed >>= (rt.targets[·]?) with
        | some t =>
          match t.action with
          | .input id _ _ =>
            if sameId rt.focus (some id) then rt.sendInput id (.drag (x - t.ox) (y - t.oy)) else rt
          | _ => rt
        | none => rt
    | .pointerLeave =>
      if rt.captured.isSome then rt
      else { rt with pointer := none, hovered := none, dirty := rt.hovered.isSome }
    | .pointerDown x y .left =>
      let p := (toPx x, toPx y)
      let hit := pressIndex rt.targets p.1 p.2
      let rt := { rt with pointer := some p, pressed := hit, hovered := hit, dirty := true }
      match hit >>= (rt.targets[·]?) with
      | some t =>
        match t.action with
        | .drag f =>
          let rt := { rt.setFocus none with captured := some t }
          rt.dispatchOpt (f (localInfo t .press x y))
        | .input id _ _ =>
          let again := sameId rt.focus (some id) && match rt.lastPress with
            | some (t0, x0, y0) => rt.time - t0 ≤ doubleClickTime && (x - x0).abs ≤ 4 && (y - y0).abs ≤ 4
            | none => false
          let (lx, ly) := (x - t.ox, y - t.oy)
          let ev : InputEvent :=
            if rt.shift && sameId rt.focus (some id) then .drag lx ly
            else if again then .doubleClick lx ly else .press lx ly
          -- a third press starts over
          let rt := { rt with lastPress := if again then none else some (rt.time, x, y) }
          (rt.setFocus (some id)).sendInput id ev
        | _ => rt.setFocus none
      | none => rt.setFocus none
    | .pointerUp x y .left =>
      let p := (toPx x, toPx y)
      let hit := pressIndex rt.targets p.1 p.2
      let wasPressed := rt.pressed
      let captured := rt.captured
      let rt := { rt with pointer := some p, pressed := none, hovered := hit, captured := none,
                          dirty := true }
      match captured with
      | some t =>
        match t.action with
        | .drag f => rt.dispatchOpt (f (localInfo t .release x y))
        | _ => rt
      | none =>
        -- a tap is a press and release on the same target
        match wasPressed, hit with
        | some i, some j => if i == j then rt.dispatchIf i else rt
        | _, _ => rt
    | .scroll _ dy =>
      match rt.pointer with
      | some (px, py) =>
        -- an input that scrolls (a text area) takes the wheel first
        let byInput := match pressIndex rt.targets px py >>= (rt.targets[·]?) with
          | some { action := .input _ f _, .. } => f (.wheel dy)
          | _ => none
        if let some m := byInput then rt.dispatch m else
        match scrollIndex rt.targets px py >>= (rt.targets[·]?) with
        | some { action := .scroll off max f, .. } =>
          let target := Min.min max (toPx (off.toF + dy))
          if target == off then rt else rt.dispatch (f target)
        | _ => rt
      | none => rt
    | .keyDown .shift => { rt with shift := true }
    | .keyUp .shift => { rt with shift := false }
    | .keyDown .ctrl => { rt with ctrl := true }
    | .keyUp .ctrl => { rt with ctrl := false }
    | .keyDown .tab =>
      if focused then rt.setFocus (rt.nextInput rt.shift) else rt
    | .keyDown .escape =>
      if focused then rt.setFocus none else rt
    | .keyDown k =>
      match rt.focus with
      | some id => rt.keyToInput id k
      | none => rt
    | .textInput s =>
      match rt.focus with
      | some id => rt.sendInput id (.text s)
      | none => rt
    | .compose s =>
      match rt.focus with
      | some id => rt.sendInput id (.compose s)
      | none => rt
    | .tick dt =>
      let time := rt.time + dt
      let blinked := rt.focus.isSome && rt.blinkOn != { rt with time }.blinkOn
      let fading := rt.hoverFade < 1
      { rt with time, hoverFade := Min.min 1 (rt.hoverFade + dt / hoverFadeTime),
                dirty := rt.dirty || blinked || fading || rt.app.animating rt.model }
    | .resize w h => { rt with width := w, height := h }.relayout
    | .quit => { rt with quit := true }
    | _ => rt
  -- keyboard events go to the focused input only
  let toInput := focused && match e with
    | .keyDown _ | .keyUp _ | .textInput _ | .compose _ => true
    | _ => false
  if toInput then rt else
  match rt.app.subscriptions e rt.model with
  | some msg => rt.dispatch msg
  | none => rt

/-- Hover/press state for painting. -/
def pointerState (rt : Runtime Model Msg) : PointerState :=
  { pos := rt.pointer, pressed := rt.pressed.isSome && sameTarget rt.pressed rt.hovered,
    overlay := rt.captured.isNone, hoverFade := rt.hoverFade, blinkOn := rt.blinkOn }

/-- The current view as render ops. -/
def ops (rt : Runtime Model Msg) : Array RenderOp := rt.tree.2.toOps 0 0 rt.pointerState

/-- Render the current frame as RGBA8 bytes (`width * height * 4`). -/
def frame (rt : Runtime Model Msg) : ByteArray :=
  (Raster.render rt.width rt.height (rt.tree.2.toOps 0 0 rt.pointerState) rt.app.background).data

/-- Render the current frame incrementally: only the windows whose content
changed since the last `present` are rasterized (see `Render/Damage.lean`).
Clears `dirty`; the pixels are then `pixels` and the changed windows `damage`. -/
def present (rt : Runtime Model Msg) : Runtime Model Msg :=
  let ops := rt.ops
  let w := rt.width; let h := rt.height; let bg := rt.app.background
  -- take the cached frame out first so its pixels are updated in place
  let prev := rt.presented
  let rt := { rt with presented := none }
  let (f, damage) := match prev with
    | some f => f.update w h ops bg
    | none => (Frame.full w h ops bg, #[⟨0, 0, w, h⟩])
  { rt with presented := some f, damage, dirty := false }

/-- RGBA8 pixels of the last `present` (empty before the first one). -/
def pixels (rt : Runtime Model Msg) : ByteArray :=
  match rt.presented with
  | some f => f.data
  | none => .empty

def framePNG (rt : Runtime Model Msg) : ByteArray :=
  Image.toPNG (Raster.render rt.width rt.height (rt.tree.2.toOps 0 0 rt.pointerState)
    rt.app.background)

/-- Feed a script of events, as a platform shell would. -/
def simulate (rt : Runtime Model Msg) (events : List Event) : Runtime Model Msg :=
  events.foldl handle rt

/-- Convenience: a full click (move, press, release) at `(x, y)`. -/
def click (x y : Float) : List Event :=
  [.pointerMove x y, .pointerDown x y .left, .pointerUp x y .left]

end Runtime

end UVL
