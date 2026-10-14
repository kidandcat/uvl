import UniversalViz.Layout.Constraints
import UniversalViz.Render.RenderOp
import UniversalViz.Render.Font

/-!
# Placed tree

The output of layout. `Placed s` is a node of size `s`; its children are stored
in `Kids s`, and **every child carries a proof that it lies inside its parent**
(`x + child.w ≤ s.w` and `y + child.h ≤ s.h`). A layout bug can therefore never
produce a child that paints outside its parent: such a tree does not type-check.
-/

namespace UViz.Layout

structure Decoration where
  fill : Option Paint := none
  radius : Float := 0
  border : Option (Float × Color) := none
  /-- Shadow blur radius and color. -/
  shadow : Option (Float × Color) := none
deriving Inhabited

/-- What a node draws behind its children. -/
inductive Visual where
  | none
  | deco (d : Decoration)
  | text (s : String) (scale : Nat) (color : Color)
  /-- Custom painter, given the node's absolute rectangle. -/
  | custom (draw : Rect → Array RenderOp)
deriving Inhabited

mutual
inductive Placed : Size → Type where
  | node (s : Size) (v : Visual) (kids : Kids s) : Placed s

inductive Kids : Size → Type where
  | nil (s : Size) : Kids s
  | cons {s : Size} (x y : Nat) (cs : Size) (child : Placed cs)
      (hx : x + cs.w ≤ s.w) (hy : y + cs.h ≤ s.h) (rest : Kids s) : Kids s
end

instance (s : Size) : Inhabited (Placed s) := ⟨.node s .none (.nil s)⟩

def Placed.leaf (s : Size) (v : Visual) : Placed s := .node s v (.nil s)

/-- A child together with its size. -/
structure Child where
  size : Size
  node : Placed size

namespace Kids

/-- Place a child that is known to fit; the offset is clamped so the result is
always in bounds (the clamp is a no-op for well-behaved layouts). -/
def place {s : Size} (x y : Nat) (c : Child) (hw : c.size.w ≤ s.w) (hh : c.size.h ≤ s.h)
    (rest : Kids s) : Kids s :=
  .cons (Min.min x (s.w - c.size.w)) (Min.min y (s.h - c.size.h)) c.size c.node
    (by omega) (by omega) rest

/-- Build the children list from positioned children that all fit in `s`. -/
def ofList {s : Size} : (items : List (Nat × Nat × Child)) →
    (∀ it ∈ items, it.2.2.size.w ≤ s.w ∧ it.2.2.size.h ≤ s.h) → Kids s
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

def Visual.toOps (v : Visual) (r : Rect) : Array RenderOp :=
  match v with
  | .none => #[]
  | .deco d => d.toOps r
  | .text s scale col => #[.clip r #[.text ⟨r.x, r.y⟩ s scale.toFloat col]]
  | .custom draw => #[.clip r (draw r)]

mutual
/-- Lower a placed tree at absolute offset `(ox, oy)` to render ops. -/
def Placed.toOps {s : Size} (ox oy : Nat) : Placed s → Array RenderOp
  | .node s v kids =>
    v.toOps ⟨ox.toFloat, oy.toFloat, s.w.toFloat, s.h.toFloat⟩ ++ Kids.toOps ox oy kids

def Kids.toOps {s : Size} (ox oy : Nat) : Kids s → Array RenderOp
  | .nil _ => #[]
  | .cons x y _ child _ _ rest => child.toOps (ox + x) (oy + y) ++ Kids.toOps ox oy rest
end

/-! ### Inspection -/

mutual
/-- Absolute rectangles `(x, y, w, h)` of every node, in paint order. -/
def Placed.rects {s : Size} (ox oy : Nat) : Placed s → List (Nat × Nat × Nat × Nat)
  | .node s _ kids => (ox, oy, s.w, s.h) :: Kids.rects ox oy kids
def Kids.rects {s : Size} (ox oy : Nat) : Kids s → List (Nat × Nat × Nat × Nat)
  | .nil _ => []
  | .cons x y _ child _ _ rest => child.rects (ox + x) (oy + y) ++ Kids.rects ox oy rest
end

end UViz.Layout
