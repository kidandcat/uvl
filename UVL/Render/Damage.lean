import UVL.Render.Tile

/-!
# Damage tracking and partial redraw

Most frames of an interactive app differ from the previous one in a small
area: a hovered button, a counter label, a blinking caret. Re-rasterizing the
whole frame for that wastes most of the frame budget.

`damage old new` compares two scenes structurally and returns device-space
rectangles that cover every pixel whose value may differ. Containers
(`group`, `transform` and `clip` with an unchanged matrix/rectangle) are
compared child by child, so a change deep in the widget tree only damages the
bounds of the changed leaf ops (old and new position).

`Frame.update` then repaints only the damaged windows with
`Raster.renderWindow`, the same routine the tile renderer uses, and copies them
into the previous frame. Because `renderWindow` produces exactly the pixels of a
full render, the result is **bit-identical** to `Raster.render` (checked by the
test suite).
-/

namespace UVL

namespace RenderOp

/-- Intersection of two rectangles, `none` when empty. -/
def Rect.inter (a b : Rect) : Option Rect :=
  let x0 := Max.max a.x b.x; let y0 := Max.max a.y b.y
  let x1 := Min.min (a.x + a.w) (b.x + b.w); let y1 := Min.min (a.y + a.h) (b.y + b.h)
  if x1 > x0 && y1 > y0 then some ⟨x0, y0, x1 - x0, y1 - y0⟩ else none

@[inline] private def pushBounds (m : Affine) (acc : Array Rect) (op : RenderOp) : Array Rect :=
  match op.bounds m with
  | some b => acc.push b
  | none => acc

-- A child is a smaller `sizeOf` than the array it lives in, and that array is
-- a smaller `sizeOf` than the container op, so comparing two scenes terminates.
mutual

/-- Damage between `a[i:]` and `b[i:]` (same length), appended to `acc`. -/
def diffZip (m : Affine) (acc : Array Rect) (a b : Array RenderOp) (i : Nat) : Array Rect :=
  if h : i < a.size then
    if h2 : i < b.size then
      diffZip m (diffOp m acc a[i] b[i]) a b (i + 1)
    else
      acc
  else
    acc
termination_by (sizeOf a + sizeOf b, a.size - i)
decreasing_by
  all_goals
    first
    | omega
    | apply Prod.Lex.left
      exact Nat.add_lt_add (Array.sizeOf_getElem a i h) (Array.sizeOf_getElem b i h2)

/-- Damage between two op sequences drawn through `m`, appended to `acc`. -/
def diffOps (m : Affine) (acc : Array Rect) (a b : Array RenderOp) : Array Rect :=
  if a.size == b.size then
    diffZip m acc a b 0
  else
    -- an insertion or removal: keep the common prefix and suffix, damage the rest
    let n := Min.min a.size b.size
    let pre := (List.range n).find? (fun i => !(a[i]! == b[i]!)) |>.getD n
    let suf := (List.range (n - pre)).find? (fun i => !(a[a.size - 1 - i]! == b[b.size - 1 - i]!))
      |>.getD (n - pre)
    let acc := (a.extract pre (a.size - suf)).foldl (pushBounds m) acc
    (b.extract pre (b.size - suf)).foldl (pushBounds m) acc
termination_by (sizeOf a + sizeOf b, a.size + 1)

/-- Damage between two ops drawn through `m`. -/
def diffOp (m : Affine) (acc : Array Rect) (x y : RenderOp) : Array Rect :=
  let changed := pushBounds m (pushBounds m acc x) y
  match x, y with
  | .group as, .group bs => diffOps m acc as bs
  | .transform m1 as, .transform m2 bs =>
    if m1 == m2 then diffOps (m.compose m1) acc as bs else changed
  | .clip r1 as, .clip r2 bs =>
    if r1 == r2 then
      -- nothing inside a clip can paint outside it
      let c := (m.mapRect r1).inflate 1.0
      (diffOps m #[] as bs).foldl (init := acc) fun acc d =>
        match Rect.inter d c with
        | some d => acc.push d
        | none => acc
    else changed
  | _, _ => if x == y then acc else changed
termination_by (sizeOf x + sizeOf y, 0)

end

end RenderOp

/-- A device pixel window `[x, x+w) × [y, y+h)`. -/
structure Window where
  x : Nat
  y : Nat
  w : Nat
  h : Nat
deriving Inhabited, Repr, BEq

namespace Window

def area (r : Window) : Nat := r.w * r.h

def union (a b : Window) : Window :=
  let x0 := Min.min a.x b.x; let y0 := Min.min a.y b.y
  ⟨x0, y0, Max.max (a.x + a.w) (b.x + b.w) - x0, Max.max (a.y + a.h) (b.y + b.h) - y0⟩

/-- Overlapping or touching (merging touching windows costs nothing extra). -/
def meets (a b : Window) : Bool :=
  a.x ≤ b.x + b.w && b.x ≤ a.x + a.w && a.y ≤ b.y + b.h && b.y ≤ a.y + a.h

/-- Clamp a device coordinate into `0 .. n`. -/
def clampPx (v : Float) (n : Nat) : Nat :=
  if v <= 0 then 0 else Min.min n v.toUInt64.toNat

theorem clampPx_le (v : Float) (n : Nat) : clampPx v n ≤ n := by
  unfold clampPx
  split
  · exact Nat.zero_le n
  · exact Nat.min_le_left n _

/-- A window from inclusive-exclusive edges, or `none` when the rectangle is empty. -/
def windowOf (x0 y0 x1 y1 : Nat) : Option Window :=
  if _ : x0 < x1 ∧ y0 < y1 then some ⟨x0, y0, x1 - x0, y1 - y0⟩ else none

/-- The pixels a device rectangle touches, clamped to a `w × h` frame. -/
def ofRect (w h : Nat) (r : Rect) : Option Window :=
  windowOf (clampPx r.x.floor w) (clampPx r.y.floor h)
    (clampPx (r.x + r.w).ceil w) (clampPx (r.y + r.h).ceil h)

/-- One left-to-right pass: union a window into an earlier one when they meet. -/
def mergePass (ws : Array Window) : Array Window :=
  ws.foldl (init := #[]) fun (acc : Array Window) r =>
    match acc.findIdx? (·.meets r) with
    | some i => acc.set! i (acc[i]!.union r)
    | none => acc.push r

-- `coalesceStep` calls `coalesceGo` at the same fuel and a lower phase, and
-- `coalesceGo` calls it at `fuel - 1`. `mergePass` is an argument, so it runs once.
mutual

def coalesceStep (ws step : Array Window) (fuel : Nat) : Array Window :=
  if step.size < ws.size then coalesceGo step fuel else step
termination_by (fuel, 1)

/-- Merge windows until a pass no longer shrinks the list. `fuel` bounds the
number of shrinks: a pass never grows the list, so `ws.size` shrinks suffice. -/
def coalesceGo (ws : Array Window) : Nat → Array Window
  | 0 => ws
  | fuel + 1 => coalesceStep ws (mergePass ws) fuel
termination_by fuel => (fuel, 0)

end

/-- Merge windows until a pass no longer shrinks the list. -/
def coalesce (ws : Array Window) : Array Window :=
  coalesceGo ws ws.size

/-- `x + w` and `y + h` stay inside a `frameW × frameH` frame. -/
def inside (frameW frameH : Nat) (win : Window) : Prop :=
  win.x + win.w ≤ frameW ∧ win.y + win.h ≤ frameH

theorem union_inside {frameW frameH : Nat} {a b : Window}
    (ha : a.inside frameW frameH) (hb : b.inside frameW frameH) :
    (a.union b).inside frameW frameH := by
  unfold inside at *
  have hx : (a.union b).x + (a.union b).w = Max.max (a.x + a.w) (b.x + b.w) := by
    unfold union
    show Min.min a.x b.x + (Max.max (a.x + a.w) (b.x + b.w) - Min.min a.x b.x)
        = Max.max (a.x + a.w) (b.x + b.w)
    exact Nat.add_sub_of_le <| Nat.le_trans (Nat.min_le_left a.x b.x)
      (Nat.le_trans (Nat.le_add_right a.x a.w) (Nat.le_max_left _ _))
  have hy : (a.union b).y + (a.union b).h = Max.max (a.y + a.h) (b.y + b.h) := by
    unfold union
    show Min.min a.y b.y + (Max.max (a.y + a.h) (b.y + b.h) - Min.min a.y b.y)
        = Max.max (a.y + a.h) (b.y + b.h)
    exact Nat.add_sub_of_le <| Nat.le_trans (Nat.min_le_left a.y b.y)
      (Nat.le_trans (Nat.le_add_right a.y a.h) (Nat.le_max_left _ _))
  rw [hx, hy]
  exact ⟨Nat.max_le.mpr ⟨ha.1, hb.1⟩, Nat.max_le.mpr ⟨ha.2, hb.2⟩⟩

theorem windowOf_inside {w h x0 y0 x1 y1 : Nat} {win : Window}
    (_hx0 : x0 ≤ w) (_hy0 : y0 ≤ h) (hx1 : x1 ≤ w) (hy1 : y1 ≤ h)
    (he : windowOf x0 y0 x1 y1 = some win) : win.inside w h := by
  unfold windowOf at he
  split at he
  · rename_i hxy
    cases he
    rcases hxy with ⟨hx, hy⟩
    change x0 + (x1 - x0) ≤ w ∧ y0 + (y1 - y0) ≤ h
    exact ⟨Nat.le_trans (Nat.le_of_eq (Nat.add_sub_of_le (Nat.le_of_lt hx))) hx1,
      Nat.le_trans (Nat.le_of_eq (Nat.add_sub_of_le (Nat.le_of_lt hy))) hy1⟩
  · cases he

theorem ofRect_inside (w h : Nat) (r : Rect) (win : Window)
    (he : ofRect w h r = some win) : win.inside w h := by
  unfold ofRect at he
  exact windowOf_inside (clampPx_le _ _) (clampPx_le _ _) (clampPx_le _ _) (clampPx_le _ _) he

private theorem mergePass_inside {frameW frameH : Nat} {ws : Array Window}
    (hw : ∀ win ∈ ws, win.inside frameW frameH) :
    ∀ win ∈ mergePass ws, win.inside frameW frameH := by
  unfold mergePass
  refine Array.foldl_induction
      (motive := fun (_ : Nat) (acc : Array Window) =>
        ∀ win : Window, win ∈ acc → win.inside frameW frameH)
      (h0 := by intro win h; simp at h) (hf := ?_)
  intro i acc hacc win hmem
  have hr : (ws[i]).inside frameW frameH :=
    hw _ (Array.mem_iff_getElem.mpr ⟨i.1, i.isLt, rfl⟩)
  cases hfind : acc.findIdx? (·.meets ws[i]) with
  | none =>
    simp only [hfind, Array.mem_push] at hmem
    rcases hmem with hmem | hmem
    · exact hacc _ hmem
    · simpa [hmem] using hr
  | some j =>
    have hj : j < acc.size := (Array.findIdx?_eq_some_iff_findIdx_eq.mp hfind).1
    simp only [hfind, Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, hj] at hmem
    rcases Array.mem_or_eq_of_mem_set (w := hj) hmem with hmem | hmem
    · exact hacc _ hmem
    · rw [hmem, getElem!_pos acc j hj]
      exact union_inside (hacc _ (Array.mem_iff_getElem.mpr ⟨j, hj, rfl⟩)) hr

private theorem coalesceGo_inside {frameW frameH fuel : Nat} {ws : Array Window}
    (hw : ∀ win ∈ ws, win.inside frameW frameH) :
    ∀ win ∈ coalesceGo ws fuel, win.inside frameW frameH := by
  induction fuel generalizing ws with
  | zero =>
    simpa [coalesceGo] using hw
  | succ fuel ih =>
    intro win hmem
    unfold coalesceGo coalesceStep at hmem
    split at hmem
    · exact ih (mergePass_inside hw) _ hmem
    · exact mergePass_inside hw _ hmem

theorem coalesce_inside {frameW frameH : Nat} {ws : Array Window}
    (hw : ∀ win ∈ ws, win.inside frameW frameH) :
    ∀ win ∈ coalesce ws, win.inside frameW frameH := by
  simpa [coalesce] using coalesceGo_inside (fuel := ws.size) hw

end Window

/-- More windows than this are merged into their bounding box: every window
re-walks the op list, so many small windows cost more than one larger one. -/
def maxDamageWindows : Nat := 6

/-- Damaged windows of a `w × h` frame going from scene `old` to scene `new`.
An empty result means the frames are identical. -/
def damage (w h : Nat) (old new : Array RenderOp) : Array Window :=
  let ws := Window.coalesce ((RenderOp.diffOps {} #[] old new).filterMap (Window.ofRect w h))
  if ws.size ≤ maxDamageWindows then ws
  else match ws[0]? with
    | some r => #[ws.foldl Window.union r]
    | none => #[]

/-- Every window reported by `damage` lies inside the frame. -/
theorem damage_inside (w h : Nat) (old new : Array RenderOp) :
    ∀ win ∈ damage w h old new, win.inside w h := by
  intro win hmem
  simp only [damage] at hmem
  generalize hwsEq :
    Window.coalesce ((RenderOp.diffOps {} #[] old new).filterMap (Window.ofRect w h)) = ws at hmem
  have hmap : ∀ win ∈ (RenderOp.diffOps {} #[] old new).filterMap (Window.ofRect w h),
      win.inside w h := by
    intro win hm
    rcases Array.mem_filterMap.mp hm with ⟨r, _, hr⟩
    exact Window.ofRect_inside w h r win hr
  have hws : ∀ win ∈ ws, win.inside w h := hwsEq ▸ Window.coalesce_inside hmap
  split at hmem
  · exact hws _ hmem
  · split at hmem
    · rename_i r hr
      have hlt : 0 < ws.size := by
        cases hsz : ws.size with
        | zero =>
          have : ¬ 0 < ws.size := by simp [hsz]
          simp [getElem?_neg ws 0 this] at hr
        | succ _ => exact Nat.zero_lt_succ _
      have heq : ws[0] = r :=
        Option.some.inj ((getElem?_pos ws 0 hlt).symm.trans hr)
      have hrIn : r.inside w h := by
        rw [← heq]
        exact hws _ (Array.mem_iff_getElem.mpr ⟨0, hlt, rfl⟩)
      have hfold : (ws.foldl Window.union r).inside w h :=
        Array.foldl_induction (motive := fun (_ : Nat) (acc : Window) => acc.inside w h)
          (h0 := hrIn) (hf := by
            intro i acc hacc
            exact Window.union_inside hacc
              (hws _ (Array.mem_iff_getElem.mpr ⟨i.1, i.isLt, rfl⟩)))
      simp only [Array.mem_def, List.mem_singleton] at hmem
      simpa [hmem] using hfold
    · simp [Array.mem_def] at hmem

/-- A rendered frame remembered together with the scene it shows. -/
structure Frame where
  width : Nat
  height : Nat
  bg : Color
  ops : Array RenderOp
  /-- RGBA8, `width * height * 4` bytes. -/
  data : ByteArray
  deriving Inhabited

namespace Frame

def full (w h : Nat) (ops : Array RenderOp) (bg : Color) : Frame :=
  { width := w, height := h, bg, ops, data := (Raster.render w h ops bg).data }

/-- Repaint only the windows of `f` that change when its scene becomes `ops`.
Returns the new frame and the windows that were repainted (the whole frame
when the size or background changed). Keep `f` unshared so its pixels are
updated in place. -/
def update (f : Frame) (w h : Nat) (ops : Array RenderOp) (bg : Color) : Frame × Array Window :=
  -- destructure first so that `data` is the only reference to the pixels
  let ⟨fw, fh, fbg, old, data⟩ := f
  if fw != w || fh != h || !(fbg == bg) || data.size != w * h * 4 then
    (full w h ops bg, #[⟨0, 0, w, h⟩])
  else
    let ws := damage w h old ops
    if ws.foldl (· + ·.area) 0 * 10 ≥ w * h * 7 then
      -- most of the frame changed: one full render is cheaper than windows
      (full w h ops bg, #[⟨0, 0, w, h⟩])
    else
      let scene := TileList.build ops
      let data := ws.foldl (init := data) fun data r =>
        let px := (Raster.renderWindow r.x r.y r.w r.h (scene.select r.x r.y r.w r.h) bg).data
        Tile.blit data w px r.w r.h r.x r.y
      ({ width := w, height := h, bg, ops, data }, ws)

end Frame

end UVL
