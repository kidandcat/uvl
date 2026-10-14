import UVL.App.Event
import UVL.UI.Basic
import UVL.Output.Image
import UVL.Render.Damage

/-!
# Elm-style application runtime

An application is `init`, a pure `update : Msg → Model → Model` and a pure
`view : Model → Widget Msg`. The runtime owns everything else: layout, hit
testing, hover/press feedback and deciding when a new frame is needed.

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
  let hovered := rt.pointer.bind fun (x, y) => hitIndex targets x y
  { rt with tree, targets, hovered, dirty := true }

def dispatch (rt : Runtime Model Msg) (msg : Msg) : Runtime Model Msg :=
  { rt with model := rt.app.update msg rt.model }.relayout

def dispatchIf (rt : Runtime Model Msg) (i : Nat) : Runtime Model Msg :=
  match rt.targets[i]? with
  | some t => rt.dispatch t.msg
  | none => rt

/-- Equality of optional target indices. Written out instead of `==` so the
compiler does not reuse a specialization that lives in the `Lean` package,
which standalone (WebAssembly) builds do not link. -/
def sameTarget : Option Nat → Option Nat → Bool
  | some a, some b => a == b
  | none, none => true
  | _, _ => false

@[inline] def toPx (v : Float) : Nat := if v <= 0 then 0 else v.floor.toUInt64.toNat

def handle (rt : Runtime Model Msg) (e : Event) : Runtime Model Msg :=
  let rt := match e with
    | .pointerMove x y =>
      let p := (toPx x, toPx y)
      let hov := hitIndex rt.targets p.1 p.2
      { rt with pointer := some p, hovered := hov,
                dirty := rt.dirty || !sameTarget hov rt.hovered || rt.pressed.isSome }
    | .pointerLeave => { rt with pointer := none, hovered := none, dirty := rt.hovered.isSome }
    | .pointerDown x y .left =>
      let p := (toPx x, toPx y)
      let hit := hitIndex rt.targets p.1 p.2
      { rt with pointer := some p, pressed := hit, hovered := hit, dirty := true }
    | .pointerUp x y .left =>
      let p := (toPx x, toPx y)
      let hit := hitIndex rt.targets p.1 p.2
      let wasPressed := rt.pressed
      let rt := { rt with pointer := some p, pressed := none, hovered := hit, dirty := true }
      -- a tap is a press and release on the same target
      match wasPressed, hit with
      | some i, some j => if i == j then rt.dispatchIf i else rt
      | _, _ => rt
    | .resize w h => { rt with width := w, height := h }.relayout
    | .quit => { rt with quit := true }
    | _ => rt
  match rt.app.subscriptions e rt.model with
  | some msg => rt.dispatch msg
  | none => rt

/-- Hover/press state for painting. -/
def pointerState (rt : Runtime Model Msg) : PointerState :=
  { pos := rt.pointer, pressed := rt.pressed.isSome && sameTarget rt.pressed rt.hovered }

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
