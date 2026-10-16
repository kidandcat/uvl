import UVL.Layout.Constraints
import UVL.Render.RenderOp
import UVL.Render.Font
import UVL.App.Event

/-!
# Placed tree

The output of layout. `Placed Msg s` is a node of size `s`; its children are
stored in `Kids Msg s`, and **every child carries a proof that it lies inside
its parent** (`x + child.w ≤ s.w` and `y + child.h ≤ s.h`). A layout bug can
therefore never produce a child that paints outside its parent: such a tree
does not type-check.

`Msg` is the application's message type: interactive nodes (`Visual.tap`,
`Visual.action`, scroll views) carry the messages to dispatch.

A scroll view (`Placed.scroll`) is the one node whose child may be taller than
the node itself: it fits horizontally (proved), and is translated by the scroll
offset and clipped to the viewport when painted and hit-tested.
-/

namespace UVL.Layout

structure Decoration where
  fill : Option Paint := none
  radius : Float := 0
  border : Option (Float × Color) := none
  /-- Shadow blur radius and color. -/
  shadow : Option (Float × Color) := none
deriving Inhabited

/-- Phase of a pointer drag on an `Action.drag` target. -/
inductive DragPhase where
  | press
  | move
  | release
deriving Inhabited, BEq, Repr

/-- A pointer event in a target's own coordinates (`x, y` from its top-left
corner, possibly outside it while dragging) and the target's size. -/
structure PointerInfo where
  phase : DragPhase
  x : Float
  y : Float
  w : Float
  h : Float
deriving Inhabited, Repr

/-- What a focusable input (`Action.input`) receives. Printable characters come
as `text`; `key` carries editing keys (arrows, backspace, …). -/
inductive InputEvent where
  | focus
  | blur
  /-- Pressed at local `(x, y)`. -/
  | press (x y : Float)
  /-- The pointer moved to local `(x, y)` while pressed (or Shift+press):
  extend the selection. -/
  | drag (x y : Float)
  | key (k : Key)
  /-- A movement key with Shift held: extend the selection. -/
  | extend (k : Key)
  /-- Ctrl (Cmd) with Left/Right (word), Home/End (whole text) or
  Backspace/Delete (delete a word); `extend` when Shift is held too. -/
  | word (k : Key) (extend : Bool)
  /-- A second press at about the same place: select the word there. -/
  | doubleClick (x y : Float)
  /-- Ctrl+Z. -/
  | undo
  /-- Ctrl+Y or Ctrl+Shift+Z. -/
  | redo
  /-- The wheel turned over the input, in pixels (positive: scroll down). -/
  | wheel (dy : Float)
  /-- An input method's uncommitted text (`""`: none). -/
  | compose (s : String)
  /-- Ctrl+A. -/
  | selectAll
  /-- Ctrl+X: the selection was copied to the clipboard, delete it. -/
  | cut
  /-- Typed or pasted text. -/
  | text (s : String)
deriving Inhabited, Repr

/-- Interactive behaviour of a node. -/
inductive Action (Msg : Type) where
  /-- Press and release on the target dispatches `msg`. -/
  | tap (msg : Msg)
  /-- The pointer is captured from press to release; every phase may dispatch. -/
  | drag (f : PointerInfo → Option Msg)
  /-- A focusable input with a stable `id`: keyboard events go to the focused one.
  `selection` is the selected text, what Ctrl+C / Ctrl+X copy to the clipboard. -/
  | input (id : String) (f : InputEvent → Option Msg) (selection : String := "")
  /-- A scroll view: wheel deltas move `offset` within `[0, max]`; `f` gets the new offset. -/
  | scroll (offset max : Nat) (f : Nat → Msg)

instance {Msg : Type} [Inhabited Msg] : Inhabited (Action Msg) := ⟨.tap default⟩

/-- Accessibility roles (what a screen reader announces). -/
inductive Role where
  | text
  | button
  | checkbox
  | slider
  | textbox
  | heading
deriving Inhabited, Repr, BEq

def Role.name : Role → String
  | .text => "text"
  | .button => "button"
  | .checkbox => "checkbox"
  | .slider => "slider"
  | .textbox => "textbox"
  | .heading => "heading"

/-- What a node means to assistive technology. An interactive node with an
empty `label` takes the text of the `text` nodes inside it. -/
structure Semantics where
  role : Role
  label : String := ""
  value : String := ""
  checked : Option Bool := none
deriving Inhabited, Repr

/-- What a node draws behind its children. -/
inductive Visual (Msg : Type) where
  | none
  | deco (d : Decoration)
  | text (s : String) (scale : Nat) (color : Color)
  /-- Custom painter, given the node's absolute rectangle. -/
  | custom (draw : Rect → Array RenderOp)
  /-- Tap target: dispatches `msg`; hover/press feedback uses corner `radius`. -/
  | tap (msg : Msg) (radius : Float)
  /-- Drag or input target (no feedback of its own). -/
  | action (a : Action Msg)
  /-- Children shown only in the "on" half of the runtime's blink cycle (a
  text caret). -/
  | blink
  /-- Accessibility information about the node (draws nothing). -/
  | semantics (s : Semantics)
deriving Inhabited

mutual
inductive Placed (Msg : Type) : Size → Type where
  | node (s : Size) (v : Visual Msg) (kids : Kids Msg s) : Placed Msg s
  /-- A `s`-sized viewport onto `content`, scrolled down by `offset` pixels
  (at most `max`); wheel events dispatch `f newOffset`. -/
  | scroll (s : Size) (offset max : Nat) (f : Nat → Msg) (cs : Size) (content : Placed Msg cs)
      (hw : cs.w ≤ s.w) : Placed Msg s

inductive Kids (Msg : Type) : Size → Type where
  | nil (s : Size) : Kids Msg s
  | cons {s : Size} (x y : Nat) (cs : Size) (child : Placed Msg cs)
      (hx : x + cs.w ≤ s.w) (hy : y + cs.h ≤ s.h) (rest : Kids Msg s) : Kids Msg s
end

variable {Msg : Type}

instance (s : Size) : Inhabited (Placed Msg s) := ⟨.node s .none (.nil s)⟩

def Placed.leaf (s : Size) (v : Visual Msg) : Placed Msg s := .node s v (.nil s)

/-- A child together with its size. -/
structure Child (Msg : Type) where
  size : Size
  node : Placed Msg size

namespace Kids

/-- Place a child that is known to fit; the offset is clamped so the result is
always in bounds (the clamp is a no-op for well-behaved layouts). -/
def place {s : Size} (x y : Nat) (c : Child Msg) (hw : c.size.w ≤ s.w) (hh : c.size.h ≤ s.h)
    (rest : Kids Msg s) : Kids Msg s :=
  .cons (Min.min x (s.w - c.size.w)) (Min.min y (s.h - c.size.h)) c.size c.node
    (by omega) (by omega) rest

/-- Build the children list from positioned children that all fit in `s`. -/
def ofList {s : Size} : (items : List (Nat × Nat × Child Msg)) →
    (∀ it ∈ items, it.2.2.size.w ≤ s.w ∧ it.2.2.size.h ≤ s.h) → Kids Msg s
  | [], _ => .nil s
  | (x, y, c) :: rest, h =>
    let hc := h (x, y, c) List.mem_cons_self
    place x y c hc.1 hc.2 (ofList rest fun it hm => h it (List.mem_cons_of_mem _ hm))

end Kids

/-! ### Lowering to render ops -/

def Decoration.toOps (d : Decoration) (r : Rect) : Array RenderOp := Id.run do
  let mut ops := #[]
  if let some (blur, col) := d.shadow then
    ops := ops.push (.shadow (r.translate ⟨0, blur / 3⟩) d.radius blur col)
  if let some p := d.fill then
    ops := ops.push (.fill (.roundedRect r (.all d.radius)) p)
  if let some (bw, col) := d.border then
    let inset := r.inflate (-bw / 2)
    ops := ops.push (.stroke (.roundedRect inset (.all (Max.max 0 (d.radius - bw / 2)))) bw col)
  return ops

/-- Pointer state used for hover/press feedback while painting. -/
structure PointerState where
  pos : Option (Nat × Nat) := none
  pressed : Bool := false
  /-- Whether tap targets draw hover/press feedback (off while dragging). -/
  overlay : Bool := true
  /-- Progress `0..1` of the hover feedback fading in. -/
  hoverFade : Float := 1
  /-- On half of the blink cycle (`Visual.blink`). -/
  blinkOn : Bool := true
deriving Inhabited

def PointerState.inside (p : PointerState) (r : Rect) : Bool :=
  match p.pos with
  | some (x, y) => r.contains ⟨x.toF + 0.5, y.toF + 0.5⟩
  | none => false

def Visual.toOps (v : Visual Msg) (r : Rect) : Array RenderOp :=
  match v with
  | .none | .tap .. | .action _ | .blink | .semantics _ => #[]
  | .deco d => d.toOps r
  | .text s scale col => #[.clip r #[.text ⟨r.x, r.y⟩ s scale.toF col]]
  | .custom draw => #[.clip r (draw r)]

/-- Feedback drawn *over* a tap target's children when hovered or pressed. -/
def Visual.overlayOps (v : Visual Msg) (r : Rect) (p : PointerState) : Array RenderOp :=
  match v with
  | .tap _ radius =>
    if p.inside r && p.overlay then
      -- hover fades in (ease out); press feedback is immediate
      let t := 1 - (1 - p.hoverFade) * (1 - p.hoverFade)
      let c := if p.pressed then Color.black.withAlpha 0.18 else Color.white.withAlpha (0.18 * t)
      #[.fill (.roundedRect r (.all radius)) c]
    else #[]
  | _ => #[]

mutual
/-- Lower a placed tree at absolute offset `(ox, oy)` to render ops. -/
def Placed.toOps {s : Size} (ox oy : Nat) (p : PointerState) : Placed Msg s → Array RenderOp
  | .node s v kids =>
    let r : Rect := ⟨ox.toF, oy.toF, s.w.toF, s.h.toF⟩
    match v with
    | .blink => if p.blinkOn then Kids.toOps ox oy p kids else #[]
    | _ => v.toOps r ++ Kids.toOps ox oy p kids ++ v.overlayOps r p
  | .scroll s offset max _ cs content _ =>
    let r : Rect := ⟨ox.toF, oy.toF, s.w.toF, s.h.toF⟩
    -- content coordinates are shifted by `offset`; the pointer only counts inside
    let p' : PointerState := { p with
      pos := if p.inside r then p.pos.map fun (x, y) => (x, y + offset) else none }
    let inner := content.toOps ox oy p'
    let bar : Array RenderOp :=
      if max == 0 then #[] else
      let th := Max.max 16.0 (s.h.toF * s.h.toF / cs.h.toF)
      let ty := oy.toF + (s.h.toF - th) * offset.toF / max.toF
      #[.fill (.roundedRect ⟨ox.toF + s.w.toF - 6, ty + 2, 4, th - 4⟩ (.all 2))
        (Color.black.withAlpha 0.3)]
    #[.clip r (#[RenderOp.translate 0 (-offset.toF) inner] ++ bar)]

def Kids.toOps {s : Size} (ox oy : Nat) (p : PointerState) : Kids Msg s → Array RenderOp
  | .nil _ => #[]
  | .cons x y _ child _ _ rest => child.toOps (ox + x) (oy + y) p ++ Kids.toOps ox oy p rest
end

/-! ### Inspection and hit testing -/

mutual
/-- Absolute rectangles `(x, y, w, h)` of every node, in paint order. -/
def Placed.rects {s : Size} (ox oy : Nat) : Placed Msg s → List (Nat × Nat × Nat × Nat)
  | .node s _ kids => (ox, oy, s.w, s.h) :: Kids.rects ox oy kids
  | .scroll s .. => [(ox, oy, s.w, s.h)]
def Kids.rects {s : Size} (ox oy : Nat) : Kids Msg s → List (Nat × Nat × Nat × Nat)
  | .nil _ => []
  | .cons x y _ child _ _ rest => child.rects (ox + x) (oy + y) ++ Kids.rects ox oy rest
end

/-- An interactive target: the absolute rectangle where it can be hit (clipped
by scroll views), the origin and size of its node (for local coordinates), and
its action. -/
structure Target (Msg : Type) where
  x : Nat
  y : Nat
  w : Nat
  h : Nat
  action : Action Msg
  /-- Absolute position of the node's top-left corner (above `y` when scrolled). -/
  ox : Float := x.toF
  oy : Float := y.toF
  fw : Nat := w
  fh : Nat := h

def Target.contains (t : Target Msg) (px py : Nat) : Bool :=
  t.x ≤ px && px < t.x + t.w && t.y ≤ py && py < t.y + t.h

/-- The message of a tap target. -/
def Target.tapMsg? (t : Target Msg) : Option Msg :=
  match t.action with
  | .tap m => some m
  | _ => none

/-- The id of an input target. -/
def Target.inputId? (t : Target Msg) : Option String :=
  match t.action with
  | .input id _ _ => some id
  | _ => none

/-- Shift a target up by `offset` and clip it to the rows `[top, bottom)`;
`none` when nothing remains visible. -/
def Target.scrolled (t : Target Msg) (offset top bottom : Nat) : Option (Target Msg) :=
  let y0 := Max.max t.y (top + offset)
  let y1 := Min.min (t.y + t.h) (bottom + offset)
  if y1 ≤ y0 then none
  else some { t with y := y0 - offset, h := y1 - y0, oy := t.oy - offset.toF }

mutual
/-- All targets, in paint order (later = on top). -/
def Placed.targets {s : Size} (ox oy : Nat) : Placed Msg s → List (Target Msg)
  | .node s v kids =>
    let here : List (Target Msg) := match v with
      | .tap msg _ => [{ x := ox, y := oy, w := s.w, h := s.h, action := .tap msg }]
      | .action a => [{ x := ox, y := oy, w := s.w, h := s.h, action := a }]
      | _ => []
    here ++ Kids.targets ox oy kids
  | .scroll s offset max f _ content _ =>
    { x := ox, y := oy, w := s.w, h := s.h, action := .scroll offset max f } ::
      (content.targets ox oy).filterMap (·.scrolled offset oy (oy + s.h))
def Kids.targets {s : Size} (ox oy : Nat) : Kids Msg s → List (Target Msg)
  | .nil _ => []
  | .cons x y _ child _ _ rest => child.targets (ox + x) (oy + y) ++ Kids.targets ox oy rest
end

/-- A node of the accessibility tree, flattened: its meaning and absolute
bounds. -/
structure SemNode where
  sem : Semantics
  x : Nat
  y : Nat
  w : Nat
  h : Nat
deriving Inhabited, Repr

private def isInteractive : Role → Bool
  | .text | .heading => false
  | _ => true

private def joinLabels (ns : List SemNode) : String :=
  ns.foldl (fun acc n => if acc.isEmpty then n.sem.label else acc ++ " " ++ n.sem.label) ""

/-- Finish an interactive node: an empty label is taken from the text inside,
which is then not announced again on its own. -/
private def withKids (n : SemNode) (kids : List SemNode) : List SemNode :=
  if isInteractive n.sem.role && n.sem.label.isEmpty then
    let texts := kids.filter fun k => !isInteractive k.sem.role
    { n with sem := { n.sem with label := joinLabels texts } } ::
      kids.filter fun k => isInteractive k.sem.role
  else n :: kids

mutual
/-- The accessibility tree in paint order. Tap targets without semantics are
buttons; scrolled-out content is left out. -/
def Placed.semantics {s : Size} (ox oy : Nat) : Placed Msg s → List SemNode
  | .node s v kids =>
    let below := Kids.semantics ox oy kids
    let at_ (sem : Semantics) : SemNode := { sem, x := ox, y := oy, w := s.w, h := s.h }
    match v with
    | .semantics sem => withKids (at_ sem) below
    | .tap .. =>
      -- an explicit role inside (a checkbox) wins
      if below.any (fun k => isInteractive k.sem.role) then below
      else withKids (at_ { role := .button }) below
    | .text str _ _ => at_ { role := .text, label := str } :: below
    | _ => below
  | .scroll s offset _ _ _ content _ =>
    (content.semantics ox oy).filterMap fun n =>
      if n.y + n.h ≤ oy + offset || n.y ≥ oy + offset + s.h then none
      else some { n with y := n.y - offset }
def Kids.semantics {s : Size} (ox oy : Nat) : Kids Msg s → List SemNode
  | .nil _ => []
  | .cons x y _ child _ _ rest => child.semantics (ox + x) (oy + y) ++ Kids.semantics ox oy rest
end

/-- Index of the topmost target under `(px, py)`. -/
def hitIndex (ts : Array (Target Msg)) (px py : Nat) : Option Nat := Id.run do
  let mut found := none
  let mut i := 0
  for t in ts do
    if t.contains px py then found := some i
    i := i + 1
  return found

/-- Index of the topmost target under `(px, py)` that is not a scroll view
(what a press or a tap reaches). -/
def pressIndex (ts : Array (Target Msg)) (px py : Nat) : Option Nat := Id.run do
  let mut found := none
  let mut i := 0
  for t in ts do
    if t.contains px py then
      match t.action with
      | .scroll .. => pure ()
      | _ => found := some i
    i := i + 1
  return found

/-- The innermost scroll view under `(px, py)`. -/
def scrollIndex (ts : Array (Target Msg)) (px py : Nat) : Option Nat := Id.run do
  let mut found := none
  let mut i := 0
  for t in ts do
    if t.contains px py then
      match t.action with
      | .scroll .. => found := some i
      | _ => pure ()
    i := i + 1
  return found

end UVL.Layout
