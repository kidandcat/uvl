import UVL.Layout.Constraints
import UVL.Render.RenderOp
import UVL.Render.Font

/-!
# Placed tree

The output of layout. `Placed Msg s` is a node of size `s`; its children are
stored in `Kids Msg s`, and **every child carries a proof that it lies inside
its parent** (`x + child.w ≤ s.w` and `y + child.h ≤ s.h`). A layout bug can
therefore never produce a child that paints outside its parent: such a tree
does not type-check.

`Msg` is the application's message type: interactive nodes (`Visual.tap`) carry
the message to dispatch when tapped.
-/

namespace UVL.Layout

structure Decoration where
  fill : Option Paint := none
  radius : Float := 0
  border : Option (Float × Color) := none
  /-- Shadow blur radius and color. -/
  shadow : Option (Float × Color) := none
deriving Inhabited

/-- What a node draws behind its children. -/
inductive Visual (Msg : Type) where
  | none
  | deco (d : Decoration)
  | text (s : String) (scale : Nat) (color : Color)
  /-- Custom painter, given the node's absolute rectangle. -/
  | custom (draw : Rect → Array RenderOp)
  /-- Tap target: dispatches `msg`; hover/press feedback uses corner `radius`. -/
  | tap (msg : Msg) (radius : Float)
deriving Inhabited

mutual
inductive Placed (Msg : Type) : Size → Type where
  | node (s : Size) (v : Visual Msg) (kids : Kids Msg s) : Placed Msg s

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
deriving Inhabited

def PointerState.inside (p : PointerState) (r : Rect) : Bool :=
  match p.pos with
  | some (x, y) => r.contains ⟨x.toF + 0.5, y.toF + 0.5⟩
  | none => false

def Visual.toOps (v : Visual Msg) (r : Rect) : Array RenderOp :=
  match v with
  | .none | .tap .. => #[]
  | .deco d => d.toOps r
  | .text s scale col => #[.clip r #[.text ⟨r.x, r.y⟩ s scale.toF col]]
  | .custom draw => #[.clip r (draw r)]

/-- Feedback drawn *over* a tap target's children when hovered or pressed. -/
def Visual.overlayOps (v : Visual Msg) (r : Rect) (p : PointerState) : Array RenderOp :=
  match v with
  | .tap _ radius =>
    if p.inside r then
      let c := if p.pressed then Color.black.withAlpha 0.18 else Color.white.withAlpha 0.18
      #[.fill (.roundedRect r (.all radius)) c]
    else #[]
  | _ => #[]

mutual
/-- Lower a placed tree at absolute offset `(ox, oy)` to render ops. -/
def Placed.toOps {s : Size} (ox oy : Nat) (p : PointerState) : Placed Msg s → Array RenderOp
  | .node s v kids =>
    let r : Rect := ⟨ox.toF, oy.toF, s.w.toF, s.h.toF⟩
    v.toOps r ++ Kids.toOps ox oy p kids ++ v.overlayOps r p

def Kids.toOps {s : Size} (ox oy : Nat) (p : PointerState) : Kids Msg s → Array RenderOp
  | .nil _ => #[]
  | .cons x y _ child _ _ rest => child.toOps (ox + x) (oy + y) p ++ Kids.toOps ox oy p rest
end

/-! ### Inspection and hit testing -/

mutual
/-- Absolute rectangles `(x, y, w, h)` of every node, in paint order. -/
def Placed.rects {s : Size} (ox oy : Nat) : Placed Msg s → List (Nat × Nat × Nat × Nat)
  | .node s _ kids => (ox, oy, s.w, s.h) :: Kids.rects ox oy kids
def Kids.rects {s : Size} (ox oy : Nat) : Kids Msg s → List (Nat × Nat × Nat × Nat)
  | .nil _ => []
  | .cons x y _ child _ _ rest => child.rects (ox + x) (oy + y) ++ Kids.rects ox oy rest
end

/-- A tap target: absolute rectangle and the message it dispatches. -/
structure Target (Msg : Type) where
  x : Nat
  y : Nat
  w : Nat
  h : Nat
  msg : Msg

def Target.contains (t : Target Msg) (px py : Nat) : Bool :=
  t.x ≤ px && px < t.x + t.w && t.y ≤ py && py < t.y + t.h

mutual
/-- All tap targets, in paint order (later = on top). -/
def Placed.targets {s : Size} (ox oy : Nat) : Placed Msg s → List (Target Msg)
  | .node s v kids =>
    let here := match v with
      | .tap msg _ => [⟨ox, oy, s.w, s.h, msg⟩]
      | _ => []
    here ++ Kids.targets ox oy kids
def Kids.targets {s : Size} (ox oy : Nat) : Kids Msg s → List (Target Msg)
  | .nil _ => []
  | .cons x y _ child _ _ rest => child.targets (ox + x) (oy + y) ++ Kids.targets ox oy rest
end

/-- Index of the topmost target under `(px, py)`. -/
def hitIndex (ts : Array (Target Msg)) (px py : Nat) : Option Nat := Id.run do
  let mut found := none
  let mut i := 0
  for t in ts do
    if t.contains px py then found := some i
    i := i + 1
  return found

end UVL.Layout
