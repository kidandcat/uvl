/-!
# Scalars: `Float` on desktop, Q16.16 fixed point on microcontrollers

The analytic shapes (boxes, rounded boxes, circles) are written once against
the `Scalar` class. The desktop rasterizer instantiates it with `Float`; on
targets without an FPU (RP2040, ESP32-C3, Cortex-M0+) it uses `Q16`, a Q16.16
fixed-point number stored in an `Int32` (`1.0 = 65536`) whose operations are
plain integer instructions.

The overflow-freedom of the fixed-point path is proved below: for every input
inside a 4096 × 4096 pixel screen, each `Int32`/`Int64` operation computes the
exact integer result (no wrap-around), and the square root is the exact
`Nat.sqrt`. See `Q16.circle_exact` and `Q16.roundedBox_exact`.
-/

namespace UVL

/-- Number-like type the distance fields are evaluated in. -/
class Scalar (α : Type) extends Add α, Sub α, Neg α, Min α, Max α where
  zero : α
  one : α
  half : α
  /-- `x < y` -/
  lt : α → α → Bool
  abs : α → α
  /-- `√(x² + y²)` -/
  hypot : α → α → α
  toFloat : α → Float

instance : Scalar Float where
  zero := 0.0
  one := 1.0
  half := 0.5
  lt x y := x < y
  abs := Float.abs
  hypot x y := Float.sqrt (x * x + y * y)
  toFloat x := x

namespace Scalar

variable {α : Type} [Scalar α]

/-- `clamp x 0 1` -/
@[inline] def clamp01 (x : α) : α := if lt x zero then zero else if lt one x then one else x

/-- Coverage of a pixel whose center is at signed distance `d` (1px box filter). -/
@[inline] def coverage (d : α) : α := clamp01 (half - d)

/-- Signed distance from `(px, py)` to the circle of center `(cx, cy)` and radius `r`. -/
@[inline] def circle (px py cx cy r : α) : α := hypot (px - cx) (py - cy) - r

/-- Radius of the corner of the quadrant that `(qx, qy)` (relative to the
center) falls in; corners are clockwise from top-left. -/
@[inline] def corner (qx qy tl tr br bl : α) : α :=
  if lt zero qx then (if lt zero qy then br else tr) else (if lt zero qy then bl else tl)

/-- Rounded box distance relative to its center, with corner radius `r`
(Inigo Quilez' formula). -/
@[inline] def roundedBoxAt (qx qy bx by_ r : α) : α :=
  let r := Min.min r (Min.min bx by_)
  let dx := abs qx - bx + r
  let dy := abs qy - by_ + r
  Min.min (Max.max dx dy) zero + hypot (Max.max dx zero) (Max.max dy zero) - r

/-- Signed distance to the box of center `(cx, cy)` and half extents `(bx, by_)`
whose corners are rounded with radii `tl tr br bl`. -/
@[inline] def roundedBox (px py cx cy bx by_ tl tr br bl : α) : α :=
  let qx := px - cx
  let qy := py - cy
  roundedBoxAt qx qy bx by_ (corner qx qy tl tr br bl)

end Scalar

/-! ## Integer square root -/

/-- `isqrtGo n r b k` adds the bits `b, b/2, …` (`k` of them) to `r` while the
square stays `≤ n`. All arithmetic is on `Int64`; `isqrt_toInt` shows it never
overflows and returns `Nat.sqrt n`. -/
def isqrtGo (n r b : Int64) : Nat → Int64
  | 0 => r
  | k + 1 =>
    let c := r + b
    isqrtGo n (if c * c ≤ n then c else r) (b / 2) k

/-- `⌊√n⌋` for `0 ≤ n < 2^62`, using only 64-bit multiplies and compares. -/
@[inline] def isqrt (n : Int64) : Int64 := isqrtGo n 0 (2 ^ 30) 31

theorem isqrtGo_spec (n r b : Int64) (k : Nat) (hr : 0 ≤ r.toInt)
    (hrk : r.toInt + 2 ^ k ≤ 2 ^ 31) (hb : b.toInt = 2 ^ k / 2)
    (hlo : r.toInt * r.toInt ≤ n.toInt) (hhi : n.toInt < (r.toInt + 2 ^ k) * (r.toInt + 2 ^ k)) :
    let s := (isqrtGo n r b k).toInt
    0 ≤ s ∧ s * s ≤ n.toInt ∧ n.toInt < (s + 1) * (s + 1) := by
  induction k generalizing r b with
  | zero => simpa [isqrtGo] using ⟨hr, hlo, hhi⟩
  | succ k ih =>
    have hk : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
    have h2 : (2 : Int) ^ (k + 1) = 2 ^ k * 2 := Int.pow_succ 2 k
    have hb' : b.toInt = 2 ^ k := by rw [hb, h2]; exact Int.mul_ediv_cancel _ (by decide)
    have hk31 : (2 : Int) ^ k ≤ 2 ^ 31 := by omega
    -- `c = r + b` and `c * c` are computed exactly
    have hc : (r + b).toInt = r.toInt + 2 ^ k := by
      rw [Int64.toInt_add, hb']; exact Int.bmod_eq_of_le (by omega) (by omega)
    have hcc : ((r + b) * (r + b)).toInt = (r.toInt + 2 ^ k) * (r.toInt + 2 ^ k) := by
      have h0 : 0 ≤ r.toInt + 2 ^ k := by omega
      have hrk' : r.toInt + 2 ^ k ≤ 2 ^ 31 := by omega
      have hm : (r.toInt + 2 ^ k) * (r.toInt + 2 ^ k) ≤ 2 ^ 31 * 2 ^ 31 :=
        Int.mul_le_mul hrk' hrk' h0 (by decide)
      rw [Int64.toInt_mul, hc]
      exact Int.bmod_eq_of_le (by have := Int.mul_nonneg h0 h0; omega) (by omega)
    have hdiv : (b / 2).toInt = 2 ^ k / 2 := by
      rw [Int64.toInt_div, hb']
      have : (2 : Int64).toInt = 2 := by decide
      rw [this, Int.tdiv_eq_ediv_of_nonneg (by omega)]
      exact Int.bmod_eq_of_le (by have := Int.ediv_nonneg (Int.le_of_lt hk) (show (0:Int) ≤ 2 by decide); omega)
        (by have := Int.ediv_le_self 2 (Int.le_of_lt hk); omega)
    simp only [isqrtGo]
    split
    · rename_i hle
      rw [Int64.le_iff_toInt_le, hcc] at hle
      apply ih (r + b) (b / 2) (by omega) (by omega) hdiv (by rw [hc]; exact hle)
      rw [hc]
      have : r.toInt + 2 ^ k + 2 ^ k = r.toInt + 2 ^ (k + 1) := by omega
      rw [this]; exact hhi
    · rename_i hle
      rw [Int64.le_iff_toInt_le, hcc] at hle
      exact ih r (b / 2) hr (by omega) hdiv hlo (by omega)

/-- `Nat.sqrt` is the unique `s` with `s² ≤ n < (s+1)²`. -/
theorem Nat.sqrt_unique {n s : Nat} (h1 : s * s ≤ n) (h2 : n < (s + 1) * (s + 1)) :
    Nat.sqrt n = s := by
  have a := Nat.sqrt_le n
  have b := Nat.lt_succ_sqrt n
  simp only [Nat.succ_eq_add_one] at b
  have : Nat.sqrt n < s + 1 := Nat.mul_self_lt_mul_self_iff.mp (Nat.lt_of_le_of_lt a h2)
  have : s < Nat.sqrt n + 1 := Nat.mul_self_lt_mul_self_iff.mp (Nat.lt_of_le_of_lt h1 b)
  omega

theorem isqrt_toInt (n : Int64) (h0 : 0 ≤ n.toInt) (h1 : n.toInt < 2 ^ 62) :
    (isqrt n).toInt = Nat.sqrt n.toInt.toNat := by
  have := isqrtGo_spec n 0 (2 ^ 30) 31 (by decide) (by decide) (by decide) (by simp; omega)
    (by simp; omega)
  simp only at this
  obtain ⟨hs, hlo, hhi⟩ := this
  unfold isqrt
  generalize (isqrtGo n 0 (2 ^ 30) 31).toInt = s at *
  have hs' : s = (s.toNat : Int) := (Int.toNat_of_nonneg hs).symm
  have hn' : n.toInt = (n.toInt.toNat : Int) := (Int.toNat_of_nonneg h0).symm
  rw [hs', hn'] at hlo hhi
  rw [hs', Nat.sqrt_unique (s := s.toNat) (by exact_mod_cast hlo) (by exact_mod_cast hhi)]

/-! ## Q16.16 fixed point -/

/-- A Q16.16 fixed-point number: the real `raw / 65536`. -/
structure Q16 where
  raw : Int32
deriving BEq, Inhabited, Repr

namespace Q16

/-- The real number represented, scaled by 2^16. -/
@[inline] def toInt (q : Q16) : Int := q.raw.toInt

@[inline] def ofRaw (r : Int32) : Q16 := ⟨r⟩
/-- Saturating conversion (NaN ↦ 0), rounded to the nearest 1/65536. -/
@[inline] def ofFloat (f : Float) : Q16 := ⟨(f * 65536.0).round.toInt32⟩
/-- `n + 1/2` (the center of pixel `n`). -/
@[inline] def pixelCenter (n : Nat) : Q16 := ⟨(n * 65536 + 32768).toInt32⟩
@[inline] def toFloat (q : Q16) : Float := q.raw.toFloat / 65536.0

@[inline] def add (a b : Q16) : Q16 := ⟨a.raw + b.raw⟩
@[inline] def sub (a b : Q16) : Q16 := ⟨a.raw - b.raw⟩
@[inline] def neg (a : Q16) : Q16 := ⟨-a.raw⟩
@[inline] def min (a b : Q16) : Q16 := if a.raw ≤ b.raw then a else b
@[inline] def max (a b : Q16) : Q16 := if a.raw ≤ b.raw then b else a
@[inline] def lt (a b : Q16) : Bool := a.raw < b.raw
@[inline] def abs (a : Q16) : Q16 := if a.raw < 0 then ⟨-a.raw⟩ else a
/-- Product, rounded toward zero (64-bit intermediate). -/
@[inline] def mul (a b : Q16) : Q16 := ⟨(a.raw.toInt64 * b.raw.toInt64 / 65536).toInt32⟩
/-- `√(a² + b²)`: exact 64-bit sum of squares, then `isqrt`, so no precision
is lost to an intermediate Q16 product. -/
@[inline] def hypot (a b : Q16) : Q16 :=
  let x := a.raw.toInt64
  let y := b.raw.toInt64
  ⟨(isqrt (x * x + y * y)).toInt32⟩
/-- `⌊q⌋` clamped at 0 (pixel counts). -/
@[inline] def floorNat (q : Q16) : Nat := (q.raw >>> 16).toNatClampNeg

instance : Add Q16 := ⟨add⟩
instance : Sub Q16 := ⟨sub⟩
instance : Neg Q16 := ⟨neg⟩
instance : Mul Q16 := ⟨mul⟩
instance : Min Q16 := ⟨min⟩
instance : Max Q16 := ⟨max⟩

instance : Scalar Q16 where
  zero := ⟨0⟩
  one := ⟨65536⟩
  half := ⟨32768⟩
  lt := lt
  abs := abs
  hypot := hypot
  toFloat := toFloat

/-- The same operations on unbounded integers (in raw units): the meaning the
fixed-point code is proved to compute. -/
@[reducible] def ideal : Scalar Int where
  zero := 0
  one := 65536
  half := 32768
  lt x y := decide (x < y)
  abs x := x.natAbs
  hypot x y := Nat.sqrt (x.natAbs * x.natAbs + y.natAbs * y.natAbs)
  toFloat x := Float.ofInt x / 65536.0

/-! ### Exactness of each operation

`toInt` of the machine result equals the integer result whenever the operands
are small enough; the bounds are in raw units (`2^16` = one pixel). -/

theorem sub_toInt (a b : Q16) (h1 : -2 ^ 31 ≤ a.toInt - b.toInt) (h2 : a.toInt - b.toInt < 2 ^ 31) :
    (a - b).toInt = a.toInt - b.toInt := by
  show (a.raw - b.raw).toInt = _
  rw [Int32.toInt_sub]; exact Int.bmod_eq_of_le (by unfold toInt at *; omega) (by unfold toInt at *; omega)

theorem add_toInt (a b : Q16) (h1 : -2 ^ 31 ≤ a.toInt + b.toInt) (h2 : a.toInt + b.toInt < 2 ^ 31) :
    (a + b).toInt = a.toInt + b.toInt := by
  show (a.raw + b.raw).toInt = _
  rw [Int32.toInt_add]; exact Int.bmod_eq_of_le (by unfold toInt at *; omega) (by unfold toInt at *; omega)

theorem min_toInt (a b : Q16) : (Min.min a b).toInt = Min.min a.toInt b.toInt := by
  show (Q16.min a b).toInt = _
  unfold Q16.min toInt; split <;> rename_i h <;> rw [Int32.le_iff_toInt_le] at h <;> omega

theorem max_toInt (a b : Q16) : (Max.max a b).toInt = Max.max a.toInt b.toInt := by
  show (Q16.max a b).toInt = _
  unfold Q16.max toInt; split <;> rename_i h <;> rw [Int32.le_iff_toInt_le] at h <;> omega

theorem abs_toInt (a : Q16) (h : -2 ^ 31 < a.toInt) : (Scalar.abs a).toInt = a.toInt.natAbs := by
  show (Q16.abs a).toInt = _
  unfold Q16.abs toInt at *
  split
  · rename_i hn
    rw [Int32.lt_iff_toInt_lt] at hn
    show (-a.raw).toInt = _
    rw [Int32.toInt_neg, Int.bmod_eq_of_le (by have := a.raw.toInt_lt; omega) (by omega)]
    have : (0 : Int32).toInt = 0 := by decide
    omega
  · rename_i hn
    rw [Int32.lt_iff_toInt_lt] at hn
    have : (0 : Int32).toInt = 0 := by decide
    omega

theorem lt_iff (a b : Q16) : Scalar.lt a b = true ↔ a.toInt < b.toInt := by
  show decide (a.raw < b.raw) = true ↔ _
  simp [Int32.lt_iff_toInt_lt, toInt]

theorem raw_natAbs (a : Q16) : a.toInt.natAbs ≤ 2 ^ 31 := by
  have := a.raw.toInt_lt; have := a.raw.le_toInt; unfold toInt; omega

/-- The 64-bit product never overflows; the result is exact (rounded toward
zero) whenever it fits in Q16.16. -/
theorem mul_toInt (a b : Q16) (h : (a.toInt * b.toInt).natAbs / 65536 < 2 ^ 31) :
    (a * b).toInt = (a.toInt * b.toInt).tdiv 65536 := by
  show (a.raw.toInt64 * b.raw.toInt64 / 65536).toInt32.toInt = _
  have hab : (a.toInt * b.toInt).natAbs ≤ 2 ^ 31 * 2 ^ 31 := by
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul a.raw_natAbs b.raw_natAbs
  have hp : (a.raw.toInt64 * b.raw.toInt64).toInt = a.toInt * b.toInt := by
    rw [Int64.toInt_mul, Int32.toInt_toInt64, Int32.toInt_toInt64]
    have hab' : (a.raw.toInt * b.raw.toInt).natAbs ≤ 2 ^ 31 * 2 ^ 31 := hab
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have h65 : (65536 : Int64).toInt = 65536 := by decide
  have hq : ((a.toInt * b.toInt).tdiv 65536).natAbs = (a.toInt * b.toInt).natAbs / 65536 :=
    Int.natAbs_tdiv _ _
  rw [Int64.toInt_toInt32, Int64.toInt_div, hp, h65,
    Int.bmod_eq_of_le (n := (a.toInt * b.toInt).tdiv 65536) (by omega) (by omega)]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-- `hypot` computes `Nat.sqrt (a² + b²)` exactly when `|a|, |b| ≤ 2^30`
(16384 px): the sum of squares fits in 62 bits and the root in 31. -/
theorem hypot_toInt (a b : Q16) (ha : a.toInt.natAbs ≤ 2 ^ 30) (hb : b.toInt.natAbs ≤ 2 ^ 30) :
    (Scalar.hypot a b).toInt =
      Nat.sqrt (a.toInt.natAbs * a.toInt.natAbs + b.toInt.natAbs * b.toInt.natAbs) := by
  show (isqrt (a.raw.toInt64 * a.raw.toInt64 + b.raw.toInt64 * b.raw.toInt64)).toInt32.toInt = _
  have haa : a.toInt.natAbs * a.toInt.natAbs ≤ 2 ^ 30 * 2 ^ 30 := Nat.mul_le_mul ha ha
  have hbb : b.toInt.natAbs * b.toInt.natAbs ≤ 2 ^ 30 * 2 ^ 30 := Nat.mul_le_mul hb hb
  have ea := Int.natAbs_mul_self' a.toInt
  have eb := Int.natAbs_mul_self' b.toInt
  have hsq (x : Q16) (hx : x.toInt.natAbs * x.toInt.natAbs ≤ 2 ^ 30 * 2 ^ 30) :
      (x.raw.toInt64 * x.raw.toInt64).toInt = x.toInt.natAbs * x.toInt.natAbs := by
    rw [Int64.toInt_mul, Int32.toInt_toInt64, ← Int.natAbs_mul_self' x.raw.toInt]
    exact Int.bmod_eq_of_le (by unfold toInt at hx; omega) (by unfold toInt at hx; omega)
  have hs : (a.raw.toInt64 * a.raw.toInt64 + b.raw.toInt64 * b.raw.toInt64).toInt =
      ((a.toInt.natAbs * a.toInt.natAbs + b.toInt.natAbs * b.toInt.natAbs : Nat) : Int) := by
    rw [Int64.toInt_add, hsq a haa, hsq b hbb]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  generalize hn : a.toInt.natAbs * a.toInt.natAbs + b.toInt.natAbs * b.toInt.natAbs = n at hs
  have hn62 : n < 2 ^ 62 := by omega
  rw [Int64.toInt_toInt32, isqrt_toInt _ (by omega) (by omega), hs, Int.toNat_natCast]
  have h1 := Nat.sqrt_le n
  have h31 : Nat.sqrt n < 2 ^ 31 := Nat.mul_self_lt_mul_self_iff.mp (by omega)
  exact Int.bmod_eq_of_le (by omega) (by omega)

section
attribute [local instance] ideal
@[simp] theorem ideal_zero : (Scalar.zero : Int) = 0 := rfl
@[simp] theorem ideal_abs (x : Int) : Scalar.abs x = (x.natAbs : Int) := rfl
@[simp] theorem ideal_hypot (x y : Int) :
    Scalar.hypot x y = (Nat.sqrt (x.natAbs * x.natAbs + y.natAbs * y.natAbs) : Int) := rfl
@[simp] theorem ideal_add (x y : Int) : @HAdd.hAdd Int Int Int (@instHAdd Int (@Scalar.toAdd Int ideal)) x y = x + y := rfl
@[simp] theorem ideal_sub (x y : Int) : @HSub.hSub Int Int Int (@instHSub Int (@Scalar.toSub Int ideal)) x y = x - y := rfl
@[simp] theorem ideal_min (x y : Int) : @Min.min Int (@Scalar.toMin Int ideal) x y = Min.min x y := rfl
@[simp] theorem ideal_max (x y : Int) : @Max.max Int (@Scalar.toMax Int ideal) x y = Max.max x y := rfl
end

theorem zero_toInt : (Scalar.zero : Q16).toInt = 0 := by decide

/-- A coordinate or length inside a 4096-pixel screen, in raw units. -/
abbrev Px (q : Q16) : Prop := q.toInt.natAbs ≤ 2 ^ 28

theorem corner_toInt (qx qy tl tr br bl : Q16) :
    (Scalar.corner qx qy tl tr br bl).toInt =
      @Scalar.corner Int ideal qx.toInt qy.toInt tl.toInt tr.toInt br.toInt bl.toInt := by
  have hl (a b : Q16) : Scalar.lt a b = @Scalar.lt Int ideal a.toInt b.toInt := by
    show decide (a.raw < b.raw) = decide (a.toInt < b.toInt)
    simp only [decide_eq_decide]; exact Int32.lt_iff_toInt_lt
  simp only [Scalar.corner, apply_ite Q16.toInt, hl, zero_toInt]
  rfl

theorem roundedBoxAt_toInt (qx qy bx by_ r : Q16)
    (hqx : qx.toInt.natAbs ≤ 2 ^ 29) (hqy : qy.toInt.natAbs ≤ 2 ^ 29) (hbx : Px bx) (hby : Px by_)
    (hr : Px r) :
    (Scalar.roundedBoxAt qx qy bx by_ r).toInt =
      @Scalar.roundedBoxAt Int ideal qx.toInt qy.toInt bx.toInt by_.toInt r.toInt := by
  simp only [Scalar.roundedBoxAt]
  have z := zero_toInt
  have er : (Min.min r (Min.min bx by_)).toInt = Min.min r.toInt (Min.min bx.toInt by_.toInt) := by
    rw [min_toInt, min_toInt]
  generalize Min.min r (Min.min bx by_) = r' at er ⊢
  have eax := abs_toInt qx (by omega)
  have eay := abs_toInt qy (by omega)
  have ex1 := sub_toInt (Scalar.abs qx) bx (by omega) (by omega)
  have ey1 := sub_toInt (Scalar.abs qy) by_ (by omega) (by omega)
  have ex := add_toInt (Scalar.abs qx - bx) r' (by omega) (by omega)
  have ey := add_toInt (Scalar.abs qy - by_) r' (by omega) (by omega)
  generalize Scalar.abs qx - bx + r' = dx at ex ⊢
  generalize Scalar.abs qy - by_ + r' = dy at ey ⊢
  have em := min_toInt (Max.max dx dy) Scalar.zero
  rw [max_toInt] at em
  have epx := max_toInt dx Scalar.zero
  have epy := max_toInt dy Scalar.zero
  have eh := hypot_toInt (Max.max dx Scalar.zero) (Max.max dy Scalar.zero) (by omega) (by omega)
  generalize Max.max dx Scalar.zero = mx at epx eh ⊢
  generalize Max.max dy Scalar.zero = my at epy eh ⊢
  rw [epx, epy] at eh
  generalize hn : (Max.max dx.toInt (Scalar.zero : Q16).toInt).natAbs *
      (Max.max dx.toInt (Scalar.zero : Q16).toInt).natAbs +
    (Max.max dy.toInt (Scalar.zero : Q16).toInt).natAbs *
      (Max.max dy.toInt (Scalar.zero : Q16).toInt).natAbs = n at eh
  have hxx : (Max.max dx.toInt (Scalar.zero : Q16).toInt).natAbs *
      (Max.max dx.toInt (Scalar.zero : Q16).toInt).natAbs ≤ 2 ^ 29 * 2 ^ 29 :=
    Nat.mul_le_mul (by omega) (by omega)
  have hyy : (Max.max dy.toInt (Scalar.zero : Q16).toInt).natAbs *
      (Max.max dy.toInt (Scalar.zero : Q16).toInt).natAbs ≤ 2 ^ 29 * 2 ^ 29 :=
    Nat.mul_le_mul (by omega) (by omega)
  have hs := Nat.sqrt_le n
  have hs30 : Nat.sqrt n < 2 ^ 30 := Nat.mul_self_lt_mul_self_iff.mp (by omega)
  have e1 := add_toInt (Min.min (Max.max dx dy) Scalar.zero) (Scalar.hypot mx my) (by omega) (by omega)
  have e2 := sub_toInt (Min.min (Max.max dx dy) Scalar.zero + Scalar.hypot mx my) r' (by omega) (by omega)
  rw [e2, e1, em, eh, ← hn, ex, ey, ex1, ey1, eax, eay, z, er]
  simp only [ideal_zero, ideal_abs, ideal_hypot, ideal_add, ideal_sub, ideal_min, ideal_max]

theorem roundedBox_exact (px py cx cy bx by_ tl tr br bl : Q16)
    (hpx : Px px) (hpy : Px py) (hcx : Px cx) (hcy : Px cy) (hbx : Px bx) (hby : Px by_)
    (htl : Px tl) (htr : Px tr) (hbr : Px br) (hbl : Px bl) :
    (Scalar.roundedBox px py cx cy bx by_ tl tr br bl).toInt =
      @Scalar.roundedBox Int ideal px.toInt py.toInt cx.toInt cy.toInt bx.toInt by_.toInt
        tl.toInt tr.toInt br.toInt bl.toInt := by
  show (Scalar.roundedBoxAt (px - cx) (py - cy) bx by_
    (Scalar.corner (px - cx) (py - cy) tl tr br bl)).toInt = _
  have ex := sub_toInt px cx (by omega) (by omega)
  have ey := sub_toInt py cy (by omega) (by omega)
  have hqx : (px - cx).toInt.natAbs ≤ 2 ^ 29 := by
    rw [ex]; unfold Px at hpx hcx; generalize px.toInt = a at *; generalize cx.toInt = b at *; omega
  have hqy : (py - cy).toInt.natAbs ≤ 2 ^ 29 := by
    rw [ey]; unfold Px at hpy hcy; generalize py.toInt = a at *; generalize cy.toInt = b at *; omega
  have ec := corner_toInt (px - cx) (py - cy) tl tr br bl
  have hc : (Scalar.corner (px - cx) (py - cy) tl tr br bl).toInt.natAbs ≤ 2 ^ 28 := by
    rw [ec]; simp only [Scalar.corner]
    split
    · split
      · exact hbr
      · exact htr
    · split
      · exact hbl
      · exact htl
  rw [roundedBoxAt_toInt _ _ _ _ _ hqx hqy hbx hby hc, ec, ex, ey]
  rfl

theorem circle_exact (px py cx cy r : Q16)
    (hpx : Px px) (hpy : Px py) (hcx : Px cx) (hcy : Px cy) (hr : Px r) :
    (Scalar.circle px py cx cy r).toInt =
      @Scalar.circle Int ideal px.toInt py.toInt cx.toInt cy.toInt r.toInt := by
  show (Scalar.hypot (px - cx) (py - cy) - r).toInt = _
  unfold Px at *
  have ex := sub_toInt px cx (by omega) (by omega)
  have ey := sub_toInt py cy (by omega) (by omega)
  have hqx : (px - cx).toInt.natAbs ≤ 2 ^ 29 := by
    rw [ex]; generalize px.toInt = a at *; generalize cx.toInt = b at *; omega
  have hqy : (py - cy).toInt.natAbs ≤ 2 ^ 29 := by
    rw [ey]; generalize py.toInt = a at *; generalize cy.toInt = b at *; omega
  have eh := hypot_toInt (px - cx) (py - cy) (by omega) (by omega)
  have hxx : (px - cx).toInt.natAbs * (px - cx).toInt.natAbs ≤ 2 ^ 29 * 2 ^ 29 :=
    Nat.mul_le_mul hqx hqx
  have hyy : (py - cy).toInt.natAbs * (py - cy).toInt.natAbs ≤ 2 ^ 29 * 2 ^ 29 :=
    Nat.mul_le_mul hqy hqy
  generalize hn : (px - cx).toInt.natAbs * (px - cx).toInt.natAbs +
    (py - cy).toInt.natAbs * (py - cy).toInt.natAbs = n at eh
  have hs := Nat.sqrt_le n
  have hs30 : Nat.sqrt n < 2 ^ 30 := Nat.mul_self_lt_mul_self_iff.mp (by omega)
  have e := sub_toInt (Scalar.hypot (px - cx) (py - cy)) r (by rw [eh]; omega) (by rw [eh]; omega)
  rw [e, eh, ← hn, ex, ey]
  rfl

end Q16
end UVL
