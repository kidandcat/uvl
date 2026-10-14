import UVL.Layout.Placed

/-!
# Widgets and the layout engine

`Widget` is the declarative description of a UI. `layout w c` lays it out under
constraints `c` and returns a `Result c`, which bundles

* the chosen size,
* a proof that the size satisfies `c` (`ok : c.Admits size`), and
* the `Placed` tree, whose children are proved to sit inside their parents.

So "a child returned a size that violates its parent's constraints" and
"a child overflows its parent" are type errors, not runtime bugs.
-/

namespace UVL.Layout

inductive Axis where
  | horizontal
  | vertical
deriving Inhabited, BEq, Repr

/-- Alignment along the cross axis (or within a stack). -/
inductive Align where
  | start
  | center
  | end_
  | stretch
deriving Inhabited, BEq, Repr

/-- Distribution of free space along the main axis. -/
inductive Justify where
  | start
  | center
  | end_
  | spaceBetween
deriving Inhabited, BEq, Repr

inductive Widget (Msg : Type) where
  | empty
  | text (s : String) (scale : Nat) (color : Color)
  /-- A box that would like to be `w × h`, filled with `paint`. -/
  | box (w h : Nat) (paint : Paint)
  /-- A custom-painted area that would like to be `w × h`. -/
  | canvas (w h : Nat) (draw : Rect → Array RenderOp)
  | padding (l t r b : Nat) (child : Widget Msg)
  | center (child : Widget Msg)
  | sized (w h : Option Nat) (child : Widget Msg)
  | decorated (d : Decoration) (child : Widget Msg)
  /-- Row (`horizontal`) or column (`vertical`). -/
  | flex (axis : Axis) (gap : Nat) (justify : Justify) (cross : Align) (children : List (Widget Msg))
  /-- Inside a row/column, take a `flex` share of the free space. -/
  | expanded (flex : Nat) (child : Widget Msg)
  | stack (h v : Align) (children : List (Widget Msg))
  /-- Tap target dispatching `msg`; `radius` shapes the hover/press feedback. -/
  | onTap (msg : Msg) (radius : Float) (child : Widget Msg)
  /-- Drag or input target around `child` (see `Action`). -/
  | action (a : Action Msg) (child : Widget Msg)
  /-- Vertical scroll view: `child` is laid out with unbounded height and shown
  through a viewport no taller than the constraints allow, scrolled by
  `offset` pixels; the wheel dispatches `onScroll newOffset`. -/
  | scroll (offset : Nat) (onScroll : Nat → Msg) (child : Widget Msg)
deriving Inhabited

variable {Msg : Type}

/-- The result of laying out under `c`: size, its proof of admissibility, and the tree. -/
structure Result (Msg : Type) (c : Constraints) where
  size : Size
  node : Placed Msg size
  ok : c.Admits size

instance (c : Constraints) : Inhabited (Result Msg c) :=
  ⟨⟨⟨c.minW, c.minH⟩, default, Nat.le_refl _, c.hw, Nat.le_refl _, c.hh⟩⟩

/-- A laid-out child that respects the maxima of `c`. -/
structure FitItem (Msg : Type) (c : Constraints) where
  child : Child Msg
  hw : child.size.w ≤ c.maxW
  hh : child.size.h ≤ c.maxH

def Result.fitWithin {c : Constraints} {a b d e : Nat} (r : Result Msg (c.within a b d e)) : FitItem Msg c :=
  ⟨⟨r.size, r.node⟩, (Constraints.le_max_of_within r.ok).1, (Constraints.le_max_of_within r.ok).2⟩

def maxOf {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | a :: l => Max.max (f a) (maxOf f l)

theorem le_maxOf {α : Type} (f : α → Nat) : ∀ {l : List α} {a : α}, a ∈ l → f a ≤ maxOf f l
  | b :: l, a, h => by
    cases h with
    | head => exact Nat.le_max_left _ _
    | tail _ h' => exact Nat.le_trans (le_maxOf f h') (Nat.le_max_right _ _)

open Constraints in
/-- Assemble a node under `c`. The size is the content size clamped into `c`
(but never smaller than any child), and children are positioned by `pos`,
which receives the final size. -/
def finish (c : Constraints) (v : Visual Msg) (contentW contentH : Nat) (kids : List (FitItem Msg c))
    (pos : Size → List (Nat × Nat)) : Result Msg c :=
  let s : Size :=
    ⟨clampN c.minW c.maxW (Max.max contentW (maxOf (·.child.size.w) kids)),
     clampN c.minH c.maxH (Max.max contentH (maxOf (·.child.size.h) kids))⟩
  let items : List (Nat × Nat × Child Msg) := ((pos s).zip kids).map fun (p, k) => (p.1, p.2, k.child)
  have hfit : ∀ it ∈ items, it.2.2.size.w ≤ s.w ∧ it.2.2.size.h ≤ s.h := by
    intro it hit
    simp only [items, List.mem_map] at hit
    obtain ⟨⟨p, k⟩, hpk, rfl⟩ := hit
    have hk : k ∈ kids := List.of_mem_zip hpk |>.2
    have h1 := le_maxOf (·.child.size.w) hk
    have h2 := le_maxOf (·.child.size.h) hk
    have h3 := k.hw
    have h4 := k.hh
    simp only [s, clampN] at h1 h2 ⊢
    omega
  ⟨s, .node s v (Kids.ofList items hfit), clampN_ge c.hw, clampN_le, clampN_ge c.hh, clampN_le⟩

/-- A node without children. -/
def leaf (c : Constraints) (want : Size) (v : Visual Msg) : Result Msg c :=
  ⟨c.constrain want, .leaf _ v, c.constrain_admits want⟩

@[inline] def alignOffset (a : Align) (space item : Nat) : Nat :=
  match a with
  | .center => (space - item) / 2
  | .end_ => space - item
  | _ => 0

def flexOf : Widget Msg → Option Nat
  | .expanded f _ => some (Max.max f 1)
  | _ => none

/-- Height available to the content of a scroll view. -/
def scrollLimit : Nat := 1000000

/-- Lay out `w` under constraints `c`. Total: recursion is on the widget tree. -/
def layout (w : Widget Msg) (c : Constraints) : Result Msg c :=
  match w with
  | .empty => leaf c ⟨0, 0⟩ .none
  | .text s scale col =>
    let (tw, th) := Font.measure s scale
    leaf c ⟨tw, th⟩ (.text s scale col)
  | .box bw bh paint => leaf c ⟨bw, bh⟩ (.deco { fill := some paint })
  | .canvas cw ch draw => leaf c ⟨cw, ch⟩ (.custom draw)
  | .padding l t r b child =>
    let dw := l + r
    let dh := t + b
    let k := (layout child (c.within (c.minW - dw) (c.maxW - dw) (c.minH - dh) (c.maxH - dh))).fitWithin
    finish c .none (k.child.size.w + dw) (k.child.size.h + dh) [k] fun _ => [(l, t)]
  | .center child =>
    let k := (layout child (c.within 0 c.maxW 0 c.maxH)).fitWithin
    finish c .none c.maxW c.maxH [k] fun s =>
      [((s.w - k.child.size.w) / 2, (s.h - k.child.size.h) / 2)]
  | .sized sw sh child =>
    let r := layout child (c.tighten sw sh)
    let ok := Constraints.admits_of_tighten r.ok
    ⟨r.size, r.node, ok⟩
  | .decorated d child =>
    let k := (layout child (c.within c.minW c.maxW c.minH c.maxH)).fitWithin
    finish c (.deco d) k.child.size.w k.child.size.h [k] fun _ => [(0, 0)]
  | .onTap msg radius child =>
    let k := (layout child (c.within c.minW c.maxW c.minH c.maxH)).fitWithin
    finish c (.tap msg radius) k.child.size.w k.child.size.h [k] fun _ => [(0, 0)]
  | .action a child =>
    let k := (layout child (c.within c.minW c.maxW c.minH c.maxH)).fitWithin
    finish c (.action a) k.child.size.w k.child.size.h [k] fun _ => [(0, 0)]
  | .scroll offset f child =>
    let r := layout child ⟨c.minW, c.maxW, 0, scrollLimit, c.hw, Nat.zero_le _⟩
    let s := c.constrain r.size
    let hw : r.size.w ≤ s.w := by
      have h := r.ok
      simp only [Constraints.Admits] at h
      simp only [s, Constraints.constrain, Constraints.clampN]
      omega
    let max := r.size.h - s.h
    ⟨s, .scroll s (Min.min offset max) max f r.size r.node hw, c.constrain_admits _⟩
  | .expanded _ child => layout child c
  | .stack ha va children =>
    let kids := children.map fun ch => (layout ch (c.within 0 c.maxW 0 c.maxH)).fitWithin
    finish c .none 0 0 kids fun s => kids.map fun k =>
      (alignOffset ha s.w k.child.size.w, alignOffset va s.h k.child.size.h)
  | .flex axis gap justify cross children =>
    let vertical := axis == .vertical
    let mainOf (s : Size) := if vertical then s.h else s.w
    let crossOf (s : Size) := if vertical then s.w else s.h
    let mainMax := if vertical then c.maxH else c.maxW
    let crossMax := if vertical then c.maxW else c.maxH
    let n := children.length
    let gaps := gap * (n - 1)
    let totalFlex := children.foldl (fun t ch => t + (flexOf ch).getD 0) 0
    -- Lay out all children with the given cross-axis bounds.
    let run (crossMin crossHi : Nat) : List (FitItem Msg c) :=
      let fit (ch : Widget Msg) (_h : ch ∈ children) (mMin mMax : Nat) : FitItem Msg c :=
        if vertical then (layout ch (c.within crossMin crossHi mMin mMax)).fitWithin
        else (layout ch (c.within mMin mMax crossMin crossHi)).fitWithin
      -- Phase 1: inflexible children, in order, each limited to the space still free.
      let (used, firstPass) := children.attach.foldl
        (init := (0, (#[] : Array (Option (FitItem Msg c)))))
        fun (used, acc) ⟨ch, hch⟩ =>
          match flexOf ch with
          | some _ => (used, acc.push none)
          | none =>
            let k := fit ch hch 0 (mainMax - gaps - used)
            (used + mainOf k.child.size, acc.push (some k))
      -- Phase 2: flexible children share the remaining space.
      let free := mainMax - gaps - used
      (children.attach.zip firstPass.toList).map fun (⟨ch, hch⟩, slot) =>
        match slot with
        | some k => k
        | none =>
          let share := free * (flexOf ch).getD 0 / Max.max totalFlex 1
          fit ch hch share share
    let kids0 := run 0 crossMax
    -- `stretch`: relayout every child at the common cross size (the largest
    -- natural one, or the parent's minimum if bigger), like CSS `align-items: stretch`.
    let kids : List (FitItem Msg c) :=
      if cross == .stretch then
        let parentMin := if vertical then c.minW else c.minH
        let target := Min.min crossMax (Max.max parentMin (maxOf (fun k => crossOf k.child.size) kids0))
        run target target
      else kids0
    let sumMain := kids.foldl (fun t k => t + mainOf k.child.size) 0
    let fillMain := totalFlex > 0 || justify != .start
    let contentMain := if fillMain then mainMax else sumMain + gaps
    let contentCross := maxOf (fun k => crossOf k.child.size) kids
    let (cw, ch) := if vertical then (contentCross, contentMain) else (contentMain, contentCross)
    finish c .none cw ch kids fun s =>
      let freeMain := mainOf s - sumMain - gaps
      let (start, extra) := match justify with
        | .start => (0, 0)
        | .center => (freeMain / 2, 0)
        | .end_ => (freeMain, 0)
        | .spaceBetween => (0, if n > 1 then freeMain / (n - 1) else 0)
      let (_, out) := kids.foldl (init := (start, (#[] : Array (Nat × Nat)))) fun (m, out) k =>
        let co := alignOffset cross (crossOf s) (crossOf k.child.size)
        let p := if vertical then (co, m) else (m, co)
        (m + mainOf k.child.size + gap + extra, out.push p)
      out.toList

/-- Lay out `w` to fill a `width × height` surface (tight constraints) and
lower it to render ops. -/
def Widget.toOps (w : Widget Msg) (width height : Nat) (p : PointerState := {}) :
    Array RenderOp :=
  let r := layout w (Constraints.tight ⟨width, height⟩)
  r.node.toOps 0 0 p

end UVL.Layout
