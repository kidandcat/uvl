import Init.Data.Rat.Lemmas

/-!
# Animation as a function of time

An animation is a pure function of elapsed time:

`value = start + (target - start) * ease(clamp(elapsed / duration))`.

Nothing is accumulated frame by frame, so a dropped frame is just a larger elapsed
time. Values and times in this file are `Rat`: the endpoint identities are exact.
`UVL.Anim.Pixel` and `UVL.Anim.Render` are the only bridge to `Float` pixels.

No proof uses `sorry`, and this file adds no axiom. `grind` closes the polynomial
identities; the inequalities are `Rat` order reasoning.
-/

namespace UVL.Anim

/-! ## Order helpers -/

theorem sub_nonneg_of_le {a b : Rat} (h : a ≤ b) : 0 ≤ b - a :=
  (Rat.le_iff_sub_nonneg a b).mp h

theorem lt_of_le_of_lt {a b c : Rat} (hab : a ≤ b) (hbc : b < c) : a < c :=
  Rat.not_le.mp fun hca => (Rat.not_le.mpr hbc) (Rat.le_trans hca hab)

theorem le_add_of_nonneg_right {a b : Rat} (h : 0 ≤ b) : a ≤ a + b := by
  have h' : a + 0 ≤ a + b := (Rat.add_le_add_left).mpr h
  simpa [Rat.add_zero] using h'

theorem min_eq_left {a b : Rat} (h : a ≤ b) : min a b = a := by
  simp only [Min.min]
  split
  · rfl
  · rename_i hn
    exact absurd h hn

theorem min_eq_right {a b : Rat} (h : b ≤ a) : min a b = b := by
  simp only [Min.min]
  split
  · rename_i hab
    exact Rat.le_antisymm hab h
  · rfl

theorem max_eq_right {a b : Rat} (h : a ≤ b) : max a b = b := by
  simp only [Max.max]
  split
  · rfl
  · rename_i hn
    exact absurd h hn

theorem max_eq_left {a b : Rat} (h : b ≤ a) : max a b = a := by
  simp only [Max.max]
  split
  · rename_i hab
    exact (Rat.le_antisymm hab h).symm
  · rfl

theorem min_le_left (a b : Rat) : min a b ≤ a := by
  by_cases h : a ≤ b
  · rw [min_eq_left h]; exact Rat.le_refl
  · have hba : b ≤ a := Rat.le_of_lt (Rat.not_le.mp h)
    rw [min_eq_right hba]; exact hba

theorem min_le_right (a b : Rat) : min a b ≤ b := by
  by_cases h : a ≤ b
  · rw [min_eq_left h]; exact h
  · have hba : b ≤ a := Rat.le_of_lt (Rat.not_le.mp h)
    rw [min_eq_right hba]; exact Rat.le_refl

theorem le_max_left (a b : Rat) : a ≤ max a b := by
  by_cases h : a ≤ b
  · rw [max_eq_right h]; exact h
  · have hba : b ≤ a := Rat.le_of_lt (Rat.not_le.mp h)
    rw [max_eq_left hba]; exact Rat.le_refl

theorem le_max_right (a b : Rat) : b ≤ max a b := by
  by_cases h : a ≤ b
  · rw [max_eq_right h]; exact Rat.le_refl
  · have hba : b ≤ a := Rat.le_of_lt (Rat.not_le.mp h)
    rw [max_eq_left hba]; exact hba

theorem max_add (a b d : Rat) : max (a + d) (b + d) = max a b + d := by
  by_cases h : a ≤ b
  · have h' : a + d ≤ b + d := (Rat.add_le_add_right).mpr h
    simp [max_eq_right h, max_eq_right h']
  · have hba : b ≤ a := Rat.le_of_lt (Rat.not_le.mp h)
    have h' : b + d ≤ a + d := (Rat.add_le_add_right).mpr hba
    simp [max_eq_left hba, max_eq_left h']

theorem sq_nonneg (a : Rat) : 0 ≤ a * a := by
  rcases @Rat.le_total a 0 with h | h
  · have hn : 0 ≤ -a := by simpa using Rat.neg_le_neg h
    have he : a * a = (-a) * (-a) := by grind
    rw [he]; exact Rat.mul_nonneg hn hn
  · exact Rat.mul_nonneg h h

theorem mul_nonneg_of_nonpos {a b : Rat} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by
  have ha' : 0 ≤ -a := by simpa using Rat.neg_le_neg ha
  have hb' : 0 ≤ -b := by simpa using Rat.neg_le_neg hb
  have h := Rat.mul_nonneg ha' hb'
  have he : (-a) * (-b) = a * b := by grind
  rwa [he] at h

theorem div_le_iff {a b c : Rat} (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b := by
  constructor
  · intro h
    have h' := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hb)
    rwa [Rat.div_mul_cancel (Rat.ne_of_gt hb)] at h'
  · intro h
    rw [← Rat.div_mul_cancel (Rat.ne_of_gt hb) (a := a)] at h
    exact Rat.le_of_mul_le_mul_right h hb

theorem le_div_iff {a b c : Rat} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  constructor
  · intro h
    have h' := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hc)
    rwa [Rat.div_mul_cancel (Rat.ne_of_gt hc)] at h'
  · intro h
    have h' : a * c ≤ b / c * c := by
      rw [Rat.div_mul_cancel (Rat.ne_of_gt hc)]; exact h
    exact Rat.le_of_mul_le_mul_right h' hc

theorem div_nonpos_of_nonpos_of_pos {a b : Rat} (ha : a ≤ 0) (hb : 0 < b) : a / b ≤ 0 := by
  rw [div_le_iff hb, Rat.zero_mul]; exact ha

theorem one_le_div_of_le {a b : Rat} (hb : 0 < b) (h : b ≤ a) : 1 ≤ a / b := by
  rw [le_div_iff hb, Rat.one_mul]; exact h

theorem neg_le_zero_of_nonneg {a : Rat} (h : 0 ≤ a) : -a ≤ 0 := by
  simpa using Rat.neg_le_neg h

theorem sub_le_sub_of_le {a b : Rat} (h : a ≤ b) : 1 - b ≤ 1 - a := by
  have h' : 1 + -b ≤ 1 + -a := (Rat.add_le_add_left).mpr (Rat.neg_le_neg h)
  simpa [Rat.sub_eq_add_neg] using h'

/-! ## Easing -/

/-- Polynomial easing curves on `Rat`.

`outBack` uses overshoot constant `17/10` (the usual `1.70158` is not rational).
It is the only curve here that leaves `[0, 1]`. A sine elastic is not a rational
function, so it stays on the unproved float `Tween` in `UVL.UI.Tween`. -/
inductive Easing where
  | linear
  | inQuad
  | outQuad
  | inOutQuad
  | inCubic
  | outCubic
  | inOutCubic
  | smoothstep
  | outBack
deriving DecidableEq, Repr, BEq, Inhabited

namespace Easing

/-- Curves for which `apply` is proved monotone, and therefore valued in `[0, 1]`, on `[0, 1]`. -/
def IsMonotone : Easing → Prop
  | .outBack => False
  | _ => True

def quad (t : Rat) : Rat := t * t

def cube (t : Rat) : Rat := t * t * t

def apply : Easing → Rat → Rat
  | .linear, t => t
  | .inQuad, t => quad t
  | .outQuad, t => t * (2 - t)
  | .inOutQuad, t => if t < 1 / 2 then 2 * quad t else 1 - 2 * quad (1 - t)
  | .inCubic, t => cube t
  | .outCubic, t => 1 - cube (1 - t)
  | .inOutCubic, t => if t < 1 / 2 then 4 * cube t else 1 - 4 * cube (1 - t)
  | .smoothstep, t => quad t * (3 - 2 * t)
  | .outBack, t =>
    let u := t - 1
    let c : Rat := 17 / 10
    1 + (c + 1) * cube u + c * quad u

/-- Every provided easing sends `0` to `0`. -/
theorem apply_zero (e : Easing) : e.apply 0 = 0 := by
  cases e <;> simp only [apply, quad, cube] <;> grind

/-- Every provided easing sends `1` to `1`. -/
theorem apply_one (e : Easing) : e.apply 1 = 1 := by
  cases e <;> simp only [apply, quad, cube] <;> grind

/-- `outBack` is outside the unit-interval claim: at `7/10` it is already past `1`. -/
theorem outBack_exceeds_one : Easing.outBack.apply (7 / 10) > 1 := by
  simp only [apply, quad, cube]; grind

private theorem quad_le_self (t : Rat) (h0 : 0 ≤ t) (h1 : t ≤ 1) : quad t ≤ t := by
  have : t * t ≤ 1 * t := Rat.mul_le_mul_of_nonneg_right h1 h0
  simpa [quad, Rat.one_mul] using this

private theorem inQuad_unit (t : Rat) (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ quad t ∧ quad t ≤ 1 :=
  ⟨Rat.mul_nonneg h0 h0, Rat.le_trans (quad_le_self t h0 h1) h1⟩

private theorem inQuad_mono (t s : Rat) (ht0 : 0 ≤ t) (hts : t ≤ s) : quad t ≤ quad s := by
  have hs0 : 0 ≤ s := Rat.le_trans ht0 hts
  have h := Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hts ht0)
    (Rat.mul_le_mul_of_nonneg_left hts hs0)
  simpa [quad] using h

private theorem cube_mono (t s : Rat) (ht0 : 0 ≤ t) (hts : t ≤ s) : cube t ≤ cube s := by
  have hsq := inQuad_mono t s ht0 hts
  have ht : 0 ≤ t := ht0
  have hs2 : 0 ≤ s * s := sq_nonneg s
  have h := Rat.le_trans (Rat.mul_le_mul_of_nonneg_right (by simpa [quad] using hsq) ht)
    (Rat.mul_le_mul_of_nonneg_left hts hs2)
  simpa [cube, quad] using h

private theorem inCubic_unit (t : Rat) (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ cube t ∧ cube t ≤ 1 := by
  have hnn : 0 ≤ cube t := Rat.mul_nonneg (Rat.mul_nonneg h0 h0) h0
  have hle : cube t ≤ t := by
    have hsq : t * t ≤ t := by simpa [quad] using quad_le_self t h0 h1
    have hmul : (t * t) * t ≤ t * t := Rat.mul_le_mul_of_nonneg_right hsq h0
    exact Rat.le_trans (by simpa [cube] using hmul) hsq
  exact ⟨hnn, Rat.le_trans hle h1⟩

private theorem outQuad_unit (t : Rat) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ t * (2 - t) ∧ t * (2 - t) ≤ 1 := by
  have h12 : (1 : Rat) ≤ 2 := by grind
  have hlo : 0 ≤ t * (2 - t) := Rat.mul_nonneg h0 (sub_nonneg_of_le (Rat.le_trans h1 h12))
  have hid : 1 - t * (2 - t) = (1 - t) * (1 - t) := by grind
  have hs : 0 ≤ 1 - t * (2 - t) := by rw [hid]; exact sq_nonneg _
  exact ⟨hlo, (Rat.le_iff_sub_nonneg _ 1).mpr hs⟩

private theorem outQuad_mono (t s : Rat) (ht0 : 0 ≤ t) (hts : t ≤ s) (hs1 : s ≤ 1) :
    t * (2 - t) ≤ s * (2 - s) := by
  have hid : s * (2 - s) - t * (2 - t) = (s - t) * (2 - (s + t)) := by grind
  have _hs0 : 0 ≤ s := Rat.le_trans ht0 hts
  have ht : t ≤ 1 := Rat.le_trans hts hs1
  have hst : s + t ≤ 1 + 1 :=
    Rat.le_trans ((Rat.add_le_add_right).mpr hs1) ((Rat.add_le_add_left).mpr ht)
  have h2 : (1 : Rat) + 1 = 2 := by grind
  rw [h2] at hst
  have hprod : 0 ≤ (s - t) * (2 - (s + t)) :=
    Rat.mul_nonneg (sub_nonneg_of_le hts) (sub_nonneg_of_le hst)
  rw [← hid] at hprod
  exact (Rat.le_iff_sub_nonneg _ _).mpr hprod

private theorem half_sq (t : Rat) (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) : t * t ≤ 1 / 4 := by
  have h2 : t * t ≤ (1 / 2) * t := Rat.mul_le_mul_of_nonneg_right h1 h0
  have h3 : (1 / 2) * t ≤ (1 / 2) * (1 / 2) :=
    Rat.mul_le_mul_of_nonneg_left h1 (by grind : (0 : Rat) ≤ 1 / 2)
  have h4 : (1 / 2) * (1 / 2) = (1 : Rat) / 4 := by grind
  have : t * t ≤ (1 / 2) * (1 / 2) := Rat.le_trans h2 h3
  rwa [h4] at this

private theorem two_half_sq (t : Rat) (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) : 2 * (t * t) ≤ 1 / 2 := by
  have hsq := half_sq t h0 h1
  have h : 2 * (t * t) ≤ 2 * (1 / 4) := Rat.mul_le_mul_of_nonneg_left hsq (by grind)
  have he : 2 * (1 / 4) = (1 : Rat) / 2 := by grind
  rwa [he] at h

private theorem cube_eighth (t : Rat) (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) : t * t * t ≤ 1 / 8 := by
  have hsq := half_sq t h0 h1
  have h5 : t * t * t ≤ (1 / 4) * t := Rat.mul_le_mul_of_nonneg_right hsq h0
  have h6 : (1 / 4) * t ≤ (1 / 4) * (1 / 2) :=
    Rat.mul_le_mul_of_nonneg_left h1 (by grind : (0 : Rat) ≤ 1 / 4)
  have h7 : (1 / 4) * (1 / 2) = (1 : Rat) / 8 := by grind
  have : t * t * t ≤ (1 / 4) * (1 / 2) := Rat.le_trans h5 h6
  rwa [h7] at this

private theorem four_cube_half (t : Rat) (h0 : 0 ≤ t) (h1 : t ≤ 1 / 2) :
    4 * (t * t * t) ≤ 1 / 2 := by
  have hc := cube_eighth t h0 h1
  have h : 4 * (t * t * t) ≤ 4 * (1 / 8) := Rat.mul_le_mul_of_nonneg_left hc (by grind)
  have he : 4 * (1 / 8) = (1 : Rat) / 2 := by grind
  rwa [he] at h

private theorem one_sub_le_half {t : Rat} (ht : 1 / 2 ≤ t) (h1 : t ≤ 1) :
    0 ≤ 1 - t ∧ 1 - t ≤ 1 / 2 := by
  refine ⟨sub_nonneg_of_le h1, ?_⟩
  have hsum : (1 : Rat) / 2 + 1 / 2 = 1 := by grind
  have hle : (1 : Rat) / 2 + 1 / 2 ≤ 1 / 2 + t := (Rat.add_le_add_left).mpr ht
  rw [hsum] at hle
  exact (Rat.le_add_iff_sub_le).mp hle

private theorem inOutQuad_unit (t : Rat) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ (if t < 1 / 2 then 2 * quad t else 1 - 2 * quad (1 - t)) ∧
      (if t < 1 / 2 then 2 * quad t else 1 - 2 * quad (1 - t)) ≤ 1 := by
  by_cases ht : t < 1 / 2
  · rw [ite_eq_left ht]
    have htle : t ≤ 1 / 2 := Rat.le_of_lt ht
    have hlo : 0 ≤ 2 * quad t :=
      Rat.mul_nonneg (by grind : (0 : Rat) ≤ 2) (by simpa [quad] using Rat.mul_nonneg h0 h0)
    have hhi : 2 * quad t ≤ 1 / 2 := by simpa [quad] using two_half_sq t h0 htle
    have hone : (1 : Rat) / 2 ≤ 1 := by grind
    exact ⟨hlo, Rat.le_trans hhi hone⟩
  · rw [ite_eq_right ht]
    have hge : 1 / 2 ≤ t := (Rat.not_lt).mp ht
    have hu := one_sub_le_half hge h1
    have hhi : 2 * quad (1 - t) ≤ 1 / 2 := by simpa [quad] using two_half_sq (1 - t) hu.1 hu.2
    have hnn : 0 ≤ 2 * quad (1 - t) :=
      Rat.mul_nonneg (by grind : (0 : Rat) ≤ 2) (by simpa [quad] using Rat.mul_nonneg hu.1 hu.1)
    have hone : (1 : Rat) / 2 ≤ 1 := by grind
    exact ⟨sub_nonneg_of_le (Rat.le_trans hhi hone), (Rat.le_iff_sub_nonneg _ 1).mpr (by
      have hid : 1 - (1 - 2 * quad (1 - t)) = 2 * quad (1 - t) := by grind
      rw [hid]; exact hnn)⟩

private theorem inOutCubic_unit (t : Rat) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ (if t < 1 / 2 then 4 * cube t else 1 - 4 * cube (1 - t)) ∧
      (if t < 1 / 2 then 4 * cube t else 1 - 4 * cube (1 - t)) ≤ 1 := by
  by_cases ht : t < 1 / 2
  · rw [ite_eq_left ht]
    have htle : t ≤ 1 / 2 := Rat.le_of_lt ht
    have hlo : 0 ≤ 4 * cube t :=
      Rat.mul_nonneg (by grind : (0 : Rat) ≤ 4) (by simpa [cube] using Rat.mul_nonneg (Rat.mul_nonneg h0 h0) h0)
    have hhi : 4 * cube t ≤ 1 / 2 := by simpa [cube] using four_cube_half t h0 htle
    have hone : (1 : Rat) / 2 ≤ 1 := by grind
    exact ⟨hlo, Rat.le_trans hhi hone⟩
  · rw [ite_eq_right ht]
    have hge : 1 / 2 ≤ t := (Rat.not_lt).mp ht
    have hu := one_sub_le_half hge h1
    have hhi : 4 * cube (1 - t) ≤ 1 / 2 := by
      simpa [cube] using four_cube_half (1 - t) hu.1 hu.2
    have hnn : 0 ≤ 4 * cube (1 - t) :=
      Rat.mul_nonneg (by grind : (0 : Rat) ≤ 4)
        (by simpa [cube] using Rat.mul_nonneg (Rat.mul_nonneg hu.1 hu.1) hu.1)
    have hone : (1 : Rat) / 2 ≤ 1 := by grind
    exact ⟨sub_nonneg_of_le (Rat.le_trans hhi hone), (Rat.le_iff_sub_nonneg _ 1).mpr (by
      have hid : 1 - (1 - 4 * cube (1 - t)) = 4 * cube (1 - t) := by grind
      rw [hid]; exact hnn)⟩

private theorem outCubic_unit (t : Rat) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ 1 - cube (1 - t) ∧ 1 - cube (1 - t) ≤ 1 := by
  have hu : 0 ≤ 1 - t := sub_nonneg_of_le h1
  have hu1 : 1 - t ≤ 1 := by
    have h' : 1 + -t ≤ 1 + 0 := (Rat.add_le_add_left).mpr (neg_le_zero_of_nonneg h0)
    simpa [Rat.sub_eq_add_neg, Rat.add_zero] using h'
  have hle : cube (1 - t) ≤ 1 - t := by
    have hsq : (1 - t) * (1 - t) ≤ 1 - t := by simpa [quad] using quad_le_self (1 - t) hu hu1
    have hmul : ((1 - t) * (1 - t)) * (1 - t) ≤ (1 - t) * (1 - t) :=
      Rat.mul_le_mul_of_nonneg_right hsq hu
    exact Rat.le_trans (by simpa [cube] using hmul) hsq
  have hnn : 0 ≤ cube (1 - t) := Rat.mul_nonneg (Rat.mul_nonneg hu hu) hu
  exact ⟨sub_nonneg_of_le (Rat.le_trans hle hu1), (Rat.le_iff_sub_nonneg _ 1).mpr (by
    have hid : 1 - (1 - cube (1 - t)) = cube (1 - t) := by grind
    rw [hid]; exact hnn)⟩

private theorem smooth_unit (t : Rat) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ quad t * (3 - 2 * t) ∧ quad t * (3 - 2 * t) ≤ 1 := by
  have ht2 : 2 * t ≤ 2 * 1 := Rat.mul_le_mul_of_nonneg_left h1 (by grind : (0 : Rat) ≤ 2)
  have h2 : 0 ≤ 2 - 2 * t := sub_nonneg_of_le (by simpa using ht2)
  have hsum : 0 ≤ 1 + (2 - 2 * t) := Rat.add_nonneg (by grind : (0 : Rat) ≤ 1) h2
  have hid3 : 1 + (2 - 2 * t) = 3 - 2 * t := by grind
  have h32 : 0 ≤ 3 - 2 * t := by rwa [hid3] at hsum
  have hlo : 0 ≤ quad t * (3 - 2 * t) := Rat.mul_nonneg (by simpa [quad] using Rat.mul_nonneg h0 h0) h32
  have hid : 1 - quad t * (3 - 2 * t) = (1 - t) * (1 - t) * (1 + 2 * t) := by
    simp only [quad]; grind
  have hfac : 0 ≤ (1 - t) * (1 - t) * (1 + 2 * t) :=
    Rat.mul_nonneg (sq_nonneg _) (Rat.add_nonneg (by grind : (0 : Rat) ≤ 1) (Rat.mul_nonneg (by grind) h0))
  have hgap : 0 ≤ 1 - quad t * (3 - 2 * t) := by rw [hid]; exact hfac
  exact ⟨hlo, (Rat.le_iff_sub_nonneg _ 1).mpr hgap⟩

private theorem inOutQuad_mono (t s : Rat) (ht0 : 0 ≤ t) (hts : t ≤ s) (hs1 : s ≤ 1) :
    (if t < 1 / 2 then 2 * quad t else 1 - 2 * quad (1 - t)) ≤
      (if s < 1 / 2 then 2 * quad s else 1 - 2 * quad (1 - s)) := by
  by_cases ht : t < 1 / 2
  · by_cases hs : s < 1 / 2
    · have hmul : 2 * quad t ≤ 2 * quad s :=
        Rat.mul_le_mul_of_nonneg_left (inQuad_mono t s ht0 hts) (by grind : (0 : Rat) ≤ 2)
      rw [ite_eq_left ht, ite_eq_left hs]; exact hmul
    · have hge : 1 / 2 ≤ s := (Rat.not_lt).mp hs
      have hleft : 2 * quad t ≤ 1 / 2 := by simpa [quad] using two_half_sq t ht0 (Rat.le_of_lt ht)
      have hu := one_sub_le_half hge hs1
      have hright : 1 / 2 ≤ 1 - 2 * quad (1 - s) := by
        have hx : 2 * quad (1 - s) ≤ 1 / 2 := by simpa [quad] using two_half_sq (1 - s) hu.1 hu.2
        have hsum : 1 / 2 + 2 * quad (1 - s) ≤ 1 / 2 + 1 / 2 := (Rat.add_le_add_left).mpr hx
        have he : (1 : Rat) / 2 + 1 / 2 = 1 := by grind
        rw [he] at hsum
        exact (Rat.le_sub_iff).mpr hsum
      rw [ite_eq_left ht, ite_eq_right hs]
      exact Rat.le_trans hleft hright
  · have hge : 1 / 2 ≤ t := (Rat.not_lt).mp ht
    have hs : ¬ s < 1 / 2 := fun hs => ht (lt_of_le_of_lt hts hs)
    have hu_s := one_sub_le_half ((Rat.not_lt).mp hs) hs1
    have hvu : 1 - s ≤ 1 - t := sub_le_sub_of_le hts
    have hquad : quad (1 - s) ≤ quad (1 - t) := inQuad_mono (1 - s) (1 - t) hu_s.1 hvu
    have h2 : 2 * quad (1 - s) ≤ 2 * quad (1 - t) :=
      Rat.mul_le_mul_of_nonneg_left hquad (by grind : (0 : Rat) ≤ 2)
    have hneg : 1 - 2 * quad (1 - t) ≤ 1 - 2 * quad (1 - s) := by
      have h' : 1 + -(2 * quad (1 - t)) ≤ 1 + -(2 * quad (1 - s)) :=
        (Rat.add_le_add_left).mpr (Rat.neg_le_neg h2)
      simpa [Rat.sub_eq_add_neg] using h'
    rw [ite_eq_right ht, ite_eq_right hs]; exact hneg

private theorem inOutCubic_mono (t s : Rat) (ht0 : 0 ≤ t) (hts : t ≤ s) (hs1 : s ≤ 1) :
    (if t < 1 / 2 then 4 * cube t else 1 - 4 * cube (1 - t)) ≤
      (if s < 1 / 2 then 4 * cube s else 1 - 4 * cube (1 - s)) := by
  by_cases ht : t < 1 / 2
  · by_cases hs : s < 1 / 2
    · have hmul : 4 * cube t ≤ 4 * cube s :=
        Rat.mul_le_mul_of_nonneg_left (cube_mono t s ht0 hts) (by grind : (0 : Rat) ≤ 4)
      rw [ite_eq_left ht, ite_eq_left hs]; exact hmul
    · have hge : 1 / 2 ≤ s := (Rat.not_lt).mp hs
      have hleft : 4 * cube t ≤ 1 / 2 := by simpa [cube] using four_cube_half t ht0 (Rat.le_of_lt ht)
      have hu := one_sub_le_half hge hs1
      have hright : 1 / 2 ≤ 1 - 4 * cube (1 - s) := by
        have hx : 4 * cube (1 - s) ≤ 1 / 2 := by simpa [cube] using four_cube_half (1 - s) hu.1 hu.2
        have hsum : 1 / 2 + 4 * cube (1 - s) ≤ 1 / 2 + 1 / 2 := (Rat.add_le_add_left).mpr hx
        have he : (1 : Rat) / 2 + 1 / 2 = 1 := by grind
        rw [he] at hsum
        exact (Rat.le_sub_iff).mpr hsum
      rw [ite_eq_left ht, ite_eq_right hs]
      exact Rat.le_trans hleft hright
  · have hs : ¬ s < 1 / 2 := fun hs => ht (lt_of_le_of_lt hts hs)
    have hu_s := one_sub_le_half ((Rat.not_lt).mp hs) hs1
    have hvu : 1 - s ≤ 1 - t := sub_le_sub_of_le hts
    have hcube : cube (1 - s) ≤ cube (1 - t) := cube_mono (1 - s) (1 - t) hu_s.1 hvu
    have h4 : 4 * cube (1 - s) ≤ 4 * cube (1 - t) :=
      Rat.mul_le_mul_of_nonneg_left hcube (by grind : (0 : Rat) ≤ 4)
    have hneg : 1 - 4 * cube (1 - t) ≤ 1 - 4 * cube (1 - s) := by
      have h' : 1 + -(4 * cube (1 - t)) ≤ 1 + -(4 * cube (1 - s)) :=
        (Rat.add_le_add_left).mpr (Rat.neg_le_neg h4)
      simpa [Rat.sub_eq_add_neg] using h'
    rw [ite_eq_right ht, ite_eq_right hs]; exact hneg

private theorem outCubic_mono (t s : Rat) (_ht0 : 0 ≤ t) (hts : t ≤ s) (hs1 : s ≤ 1) :
    1 - cube (1 - t) ≤ 1 - cube (1 - s) := by
  have hu : 0 ≤ 1 - s := sub_nonneg_of_le hs1
  have hvu : 1 - s ≤ 1 - t := sub_le_sub_of_le hts
  have hcube : cube (1 - s) ≤ cube (1 - t) := cube_mono (1 - s) (1 - t) hu hvu
  have h' : 1 + -(cube (1 - t)) ≤ 1 + -(cube (1 - s)) :=
    (Rat.add_le_add_left).mpr (Rat.neg_le_neg hcube)
  simpa [Rat.sub_eq_add_neg] using h'

private theorem smooth_lower (s t : Rat) :
    (3 * (s + t) - 2 * (s * s + s * t + t * t)) - (s * (1 - 2 * t) + 3 * t - 2 * t * t) =
      2 * s - 2 * (s * s) := by grind

private theorem smooth_at_one (t : Rat) :
    1 * (1 - 2 * t) + 3 * t - 2 * t * t = (1 - t) * (1 + 2 * t) := by grind

private theorem smooth_shift (s t : Rat) :
    (s * (1 - 2 * t) + 3 * t - 2 * t * t) - (1 * (1 - 2 * t) + 3 * t - 2 * t * t) =
      (s - 1) * (1 - 2 * t) := by grind

private theorem factor_tail (t : Rat) : 3 * t - 2 * t * t = t * (3 - 2 * t) := by grind

private theorem two_nonneg : (0 : Rat) ≤ 2 := by grind

private theorem add_sub_assoc (a b c : Rat) : a + (b - c) = a + b - c := by grind

private theorem smooth_mono (t s : Rat) (ht0 : 0 ≤ t) (hts : t ≤ s) (hs1 : s ≤ 1) :
    quad t * (3 - 2 * t) ≤ quad s * (3 - 2 * s) := by
  have hid : quad s * (3 - 2 * s) - quad t * (3 - 2 * t) =
      (s - t) * (3 * (s + t) - 2 * (s * s + s * t + t * t)) := by
    simp only [quad]; grind
  let g : Rat := 3 * (s + t) - 2 * (s * s + s * t + t * t)
  let L : Rat := s * (1 - 2 * t) + 3 * t - 2 * t * t
  have hs0 : 0 ≤ s := Rat.le_trans ht0 hts
  have hsq : s * s ≤ s := by simpa [quad] using quad_le_self s hs0 hs1
  have h2 : 2 * (s * s) ≤ 2 * s := Rat.mul_le_mul_of_nonneg_left hsq (by grind : (0 : Rat) ≤ 2)
  have hdrop : 0 ≤ g - L := by rw [smooth_lower]; exact sub_nonneg_of_le h2
  have hL : 0 ≤ L := by
    by_cases ht : t ≤ 1 / 2
    · have hcoef : 0 ≤ 1 - 2 * t := by
        have hmul : 2 * t ≤ 2 * (1 / 2) := Rat.mul_le_mul_of_nonneg_left ht (by grind)
        have he : 2 * (1 / 2) = (1 : Rat) := by grind
        rw [he] at hmul
        exact sub_nonneg_of_le hmul
      have htail : 0 ≤ 3 * t - 2 * t * t := by
        have h32 : 0 ≤ 3 - 2 * t := by
          have hm : 2 * t ≤ 2 * 1 := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans hts hs1) two_nonneg
          have h0 : 0 ≤ 2 - 2 * t := sub_nonneg_of_le (by simpa using hm)
          have hsum : 0 ≤ 1 + (2 - 2 * t) := Rat.add_nonneg (by grind : (0 : Rat) ≤ 1) h0
          have heq : 1 + (2 - 2 * t) = 3 - 2 * t := by grind
          rwa [heq] at hsum
        rw [factor_tail]; exact Rat.mul_nonneg ht0 h32
      have hsum := Rat.add_nonneg (Rat.mul_nonneg hs0 hcoef) htail
      rw [show L = s * (1 - 2 * t) + (3 * t - 2 * t * t) from by
        simp only [L, add_sub_assoc]]
      exact hsum
    · have ht' : 1 / 2 ≤ t := Rat.le_of_lt (Rat.not_le.mp ht)
      have hone : (1 : Rat) ≤ 2 * t := by
        have hmul : 2 * (1 / 2) ≤ 2 * t := Rat.mul_le_mul_of_nonneg_left ht' (by grind)
        simpa [show (2 : Rat) * (1 / 2) = 1 by grind] using hmul
      have hcoef : 1 - 2 * t ≤ 0 := by
        have hnn : 0 ≤ 2 * t - 1 := sub_nonneg_of_le hone
        have heq : 1 - 2 * t = -(2 * t - 1) := by grind
        rw [heq]; exact neg_le_zero_of_nonneg hnn
      let L1 : Rat := 1 * (1 - 2 * t) + 3 * t - 2 * t * t
      have hL1 : 0 ≤ L1 := by
        show 0 ≤ 1 * (1 - 2 * t) + 3 * t - 2 * t * t
        rw [smooth_at_one]
        exact Rat.mul_nonneg (sub_nonneg_of_le (Rat.le_trans hts hs1))
          (Rat.add_nonneg (by grind : (0 : Rat) ≤ 1) (Rat.mul_nonneg (by grind : (0 : Rat) ≤ 2) ht0))
      have hsneg : s - 1 ≤ 0 := by
        have heq : s - 1 = -(1 - s) := by grind
        rw [heq]; exact neg_le_zero_of_nonneg (sub_nonneg_of_le hs1)
      have hshift : 0 ≤ L - L1 := by
        rw [smooth_shift]; exact mul_nonneg_of_nonpos hsneg hcoef
      exact Rat.le_trans hL1 ((Rat.le_iff_sub_nonneg _ _).mpr hshift)
  have hg : 0 ≤ g := Rat.le_trans hL ((Rat.le_iff_sub_nonneg _ _).mpr hdrop)
  have hprod : 0 ≤ (s - t) * g := Rat.mul_nonneg (sub_nonneg_of_le hts) hg
  have : 0 ≤ quad s * (3 - 2 * s) - quad t * (3 - 2 * t) := by
    rw [hid]; simpa [g] using hprod
  exact (Rat.le_iff_sub_nonneg _ _).mpr this

/-- On `[0, 1]`, every monotone easing lands in `[0, 1]`. -/
theorem apply_unitInterval (e : Easing) (t : Rat) (hm : e.IsMonotone) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ e.apply t ∧ e.apply t ≤ 1 := by
  cases e with
  | linear => exact ⟨h0, h1⟩
  | inQuad => simpa [apply] using inQuad_unit t h0 h1
  | outQuad => simpa [apply] using outQuad_unit t h0 h1
  | inOutQuad => simpa [apply] using inOutQuad_unit t h0 h1
  | inCubic => simpa [apply] using inCubic_unit t h0 h1
  | outCubic => simpa [apply] using outCubic_unit t h0 h1
  | inOutCubic => simpa [apply] using inOutCubic_unit t h0 h1
  | smoothstep => simpa [apply] using smooth_unit t h0 h1
  | outBack => cases hm

/-- On `[0, 1]`, every monotone easing preserves order. -/
theorem apply_monotone (e : Easing) (t s : Rat) (hm : e.IsMonotone)
    (ht0 : 0 ≤ t) (hts : t ≤ s) (hs1 : s ≤ 1) : e.apply t ≤ e.apply s := by
  cases e with
  | linear => exact hts
  | inQuad => simpa [apply] using inQuad_mono t s ht0 hts
  | outQuad => simpa [apply] using outQuad_mono t s ht0 hts hs1
  | inOutQuad => simpa [apply] using inOutQuad_mono t s ht0 hts hs1
  | inCubic => simpa [apply] using cube_mono t s ht0 hts
  | outCubic => simpa [apply] using outCubic_mono t s ht0 hts hs1
  | inOutCubic => simpa [apply] using inOutCubic_mono t s ht0 hts hs1
  | smoothstep => simpa [apply] using smooth_mono t s ht0 hts hs1
  | outBack => cases hm

end Easing

/-! ## Sampling -/

/-- `x` lies in the closed interval with endpoints `a` and `b`, in either order. -/
def between (a b x : Rat) : Prop := min a b ≤ x ∧ x ≤ max a b

theorem between_left (a b : Rat) : between a b a :=
  ⟨min_le_left a b, le_max_left a b⟩

theorem between_right (a b : Rat) : between a b b :=
  ⟨min_le_right a b, le_max_right a b⟩

def clamp01 (t : Rat) : Rat :=
  if t ≤ 0 then 0 else if 1 ≤ t then 1 else t

/-- Elapsed fraction in `[0, 1]`. A non-positive duration is already finished (`1`). -/
def progress (duration elapsed : Rat) : Rat :=
  if duration ≤ 0 then 1 else clamp01 (elapsed / duration)

theorem progress_bounds (duration elapsed : Rat) : 0 ≤ progress duration elapsed ∧ progress duration elapsed ≤ 1 := by
  unfold progress
  split
  · exact ⟨by grind, Rat.le_refl⟩
  · unfold clamp01
    split
    · exact ⟨Rat.le_refl, by grind⟩
    · split
      · exact ⟨by grind, Rat.le_refl⟩
      · rename_i h0 h1
        exact ⟨Rat.le_of_lt (Rat.not_le.mp h0), Rat.le_of_lt (Rat.not_le.mp h1)⟩

theorem progress_le_zero (duration elapsed : Rat) (hd : 0 < duration) (he : elapsed ≤ 0) :
    progress duration elapsed = 0 := by
  have hnot : ¬ duration ≤ 0 := Rat.not_le.mpr hd
  simp only [progress, hnot, ite_false]
  have hq : elapsed / duration ≤ 0 := div_nonpos_of_nonpos_of_pos he hd
  simp [clamp01, hq]

theorem progress_ge (duration elapsed : Rat) (h : duration ≤ elapsed) : progress duration elapsed = 1 := by
  unfold progress
  split
  · rfl
  · rename_i hd
    have hdpos : 0 < duration := Rat.not_le.mp hd
    have h1 : 1 ≤ elapsed / duration := one_le_div_of_le hdpos h
    have hnot : ¬ elapsed / duration ≤ 0 := by
      intro hle
      exact (Rat.not_le.mpr (by grind : (0 : Rat) < 1)) (Rat.le_trans h1 hle)
    simp [clamp01, hnot, h1]

def lerp (a b p : Rat) : Rat := a + (b - a) * p

theorem lerp_zero (a b : Rat) : lerp a b 0 = a := by unfold lerp; grind

theorem lerp_one (a b : Rat) : lerp a b 1 = b := by unfold lerp; grind

theorem lerp_between (a b p : Rat) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : between a b (lerp a b p) := by
  have hstart : lerp a b p - a = (b - a) * p := by unfold lerp; grind
  have hend : b - lerp a b p = (b - a) * (1 - p) := by unfold lerp; grind
  have hp : 0 ≤ 1 - p := sub_nonneg_of_le hp1
  by_cases hab : a ≤ b
  · have hspan : 0 ≤ b - a := sub_nonneg_of_le hab
    have hL : a ≤ lerp a b p :=
      (Rat.le_iff_sub_nonneg a _).mpr (by rw [hstart]; exact Rat.mul_nonneg hspan hp0)
    have hR : lerp a b p ≤ b :=
      (Rat.le_iff_sub_nonneg _ b).mpr (by rw [hend]; exact Rat.mul_nonneg hspan hp)
    rw [between, min_eq_left hab, max_eq_right hab]
    exact ⟨hL, hR⟩
  · have hba : b ≤ a := Rat.le_of_lt (Rat.not_le.mp hab)
    have hspan : 0 ≤ a - b := sub_nonneg_of_le hba
    have hLb : lerp a b p - b = (a - b) * (1 - p) := by unfold lerp; grind
    have hRa : a - lerp a b p = (a - b) * p := by unfold lerp; grind
    have hL : b ≤ lerp a b p :=
      (Rat.le_iff_sub_nonneg b _).mpr (by rw [hLb]; exact Rat.mul_nonneg hspan hp)
    have hR : lerp a b p ≤ a :=
      (Rat.le_iff_sub_nonneg _ a).mpr (by rw [hRa]; exact Rat.mul_nonneg hspan hp0)
    rw [between, min_eq_right hba, max_eq_left hba]
    exact ⟨hL, hR⟩

/-- The value of one easing from `start` toward `target`. Depends only on `elapsed`. -/
def sample (e : Easing) (start target duration elapsed : Rat) : Rat :=
  lerp start target (e.apply (progress duration elapsed))

/-- At and before local time `0`, a positive-duration clip is exactly `start`. -/
theorem sample_le_zero (e : Easing) (start target duration elapsed : Rat)
    (hd : 0 < duration) (he : elapsed ≤ 0) :
    sample e start target duration elapsed = start := by
  unfold sample
  rw [progress_le_zero duration elapsed hd he, Easing.apply_zero, lerp_zero]

/-- At and after `duration` the value is exactly `target`, however large `elapsed` is. -/
theorem sample_ge_duration (e : Easing) (start target duration elapsed : Rat) (h : duration ≤ elapsed) :
    sample e start target duration elapsed = target := by
  unfold sample
  rw [progress_ge duration elapsed h, Easing.apply_one, lerp_one]

/-- A non-positive duration is already at `target` for every time, including negative times. -/
theorem sample_nonpos_duration (e : Easing) (start target duration elapsed : Rat) (hd : duration ≤ 0) :
    sample e start target duration elapsed = target := by
  have hp : progress duration elapsed = 1 := by simp [progress, hd]
  unfold sample
  rw [hp, Easing.apply_one, lerp_one]

/-- Monotone easings never leave the interval with endpoints `start` and `target`. -/
theorem sample_between (e : Easing) (start target duration elapsed : Rat) (hm : e.IsMonotone) :
    between start target (sample e start target duration elapsed) := by
  unfold sample
  have hb := progress_bounds duration elapsed
  have hu := Easing.apply_unitInterval e (progress duration elapsed) hm hb.1 hb.2
  exact lerp_between start target _ hu.1 hu.2

theorem foldl_add_eq_sum (l : List Rat) (acc : Rat) : l.foldl (· + ·) acc = acc + l.sum := by
  induction l generalizing acc with
  | nil => simp [Rat.add_zero]
  | cons a l ih =>
    simp only [List.foldl_cons, List.sum_cons, ih]
    grind

/-- Value after adding frame deltas one by one. Equal to sampling their sum. -/
def stepped (e : Easing) (start target duration : Rat) (dts : List Rat) : Rat :=
  sample e start target duration (dts.foldl (· + ·) 0)

theorem stepped_eq_sample (e : Easing) (start target duration : Rat) (dts : List Rat) :
    stepped e start target duration dts = sample e start target duration dts.sum := by
  simp [stepped, foldl_add_eq_sum, Rat.zero_add]

/-- Two frame schedules with the same total time produce the same value. -/
theorem schedules_agree (e : Easing) (start target duration : Rat) (a b : List Rat) (h : a.sum = b.sum) :
    stepped e start target duration a = stepped e start target duration b := by
  simp [stepped_eq_sample, h]

/-- One frame that jumps past the end lands on `target`, not beyond it. -/
theorem stepped_past_end (e : Easing) (start target duration dt : Rat) (h : duration ≤ dt) :
    stepped e start target duration [dt] = target := by
  have hs : ([dt] : List Rat).sum = dt := by simp [Rat.add_zero]
  rw [stepped_eq_sample, hs]
  exact sample_ge_duration e start target duration dt h

/-! ## A clip, retargeting, reversal, cancel -/

structure Clip where
  start : Rat
  target : Rat
  duration : Rat
  easing : Easing
deriving Repr, Inhabited

namespace Clip

def sample (c : Clip) (elapsed : Rat) : Rat :=
  Anim.sample c.easing c.start c.target c.duration elapsed

theorem sample_le_zero (c : Clip) (elapsed : Rat) (hd : 0 < c.duration) (he : elapsed ≤ 0) :
    c.sample elapsed = c.start :=
  Anim.sample_le_zero c.easing c.start c.target c.duration elapsed hd he

theorem sample_ge_duration (c : Clip) (elapsed : Rat) (h : c.duration ≤ elapsed) :
    c.sample elapsed = c.target :=
  Anim.sample_ge_duration c.easing c.start c.target c.duration elapsed h

theorem sample_nonpos_duration (c : Clip) (elapsed : Rat) (hd : c.duration ≤ 0) :
    c.sample elapsed = c.target :=
  Anim.sample_nonpos_duration c.easing c.start c.target c.duration elapsed hd

theorem sample_between (c : Clip) (elapsed : Rat) (hm : c.easing.IsMonotone) :
    between c.start c.target (c.sample elapsed) :=
  Anim.sample_between c.easing c.start c.target c.duration elapsed hm

/-- Same duration and the same elapsed time: both clips are exactly at their own targets. -/
theorem same_duration_sync (a b : Clip) (t : Rat) (hd : a.duration = b.duration) (ht : a.duration ≤ t) :
    a.sample t = a.target ∧ b.sample t = b.target := by
  exact ⟨a.sample_ge_duration t ht, b.sample_ge_duration t (hd ▸ ht)⟩

def stepped (c : Clip) (dts : List Rat) : Rat :=
  Anim.stepped c.easing c.start c.target c.duration dts

theorem stepped_eq_sample (c : Clip) (dts : List Rat) : c.stepped dts = c.sample dts.sum :=
  Anim.stepped_eq_sample c.easing c.start c.target c.duration dts

theorem schedules_agree (c : Clip) (a b : List Rat) (h : a.sum = b.sum) :
    c.stepped a = c.stepped b :=
  Anim.schedules_agree c.easing c.start c.target c.duration a b h

theorem stepped_past_end (c : Clip) (dt : Rat) (h : c.duration ≤ dt) : c.stepped [dt] = c.target :=
  Anim.stepped_past_end c.easing c.start c.target c.duration dt h

/-- Continue toward `v` from the value at `elapsed`, restarting local time. -/
def retarget (c : Clip) (elapsed v dur : Rat) : Clip where
  start := c.sample elapsed
  target := v
  duration := dur
  easing := c.easing

/-- Retargeting with a positive duration does not jump: time `0` of the new clip is the old value. -/
theorem retarget_continuous (c : Clip) (elapsed v dur : Rat) (hd : 0 < dur) :
    (c.retarget elapsed v dur).sample 0 = c.sample elapsed := by
  simp [retarget, sample, Anim.sample_le_zero, hd]

/-- After the new duration, a retargeted clip is exactly the new target. -/
theorem retarget_ge_duration (c : Clip) (elapsed v dur t : Rat) (h : dur ≤ t) :
    (c.retarget elapsed v dur).sample t = v := by
  simp [retarget, sample, Anim.sample_ge_duration, h]

/-- Head back to the original `start` over `dur` (default: the clip's duration). -/
def reverse (c : Clip) (elapsed : Rat) (dur : Rat := c.duration) : Clip :=
  c.retarget elapsed c.start dur

theorem reverse_continuous (c : Clip) (elapsed dur : Rat) (hd : 0 < dur) :
    (c.reverse elapsed dur).sample 0 = c.sample elapsed :=
  c.retarget_continuous elapsed c.start dur hd

/-- A reversal ends exactly at the original start. -/
theorem reverse_ge_duration (c : Clip) (elapsed dur t : Rat) (h : dur ≤ t) :
    (c.reverse elapsed dur).sample t = c.start :=
  c.retarget_ge_duration elapsed c.start dur t h

/-- What cancelling does to the value. `snapToEnd` is the target; `hold` is the current sample. -/
inductive CancelPolicy where
  | snapToEnd
  | hold
deriving DecidableEq, Repr, Inhabited

def cancelValue (c : Clip) (elapsed : Rat) : CancelPolicy → Rat
  | .snapToEnd => c.target
  | .hold => c.sample elapsed

theorem cancelValue_snap (c : Clip) (elapsed : Rat) : c.cancelValue elapsed .snapToEnd = c.target := rfl

theorem cancelValue_hold (c : Clip) (elapsed : Rat) : c.cancelValue elapsed .hold = c.sample elapsed := rfl

theorem cancelValue_between (c : Clip) (elapsed : Rat) (hm : c.easing.IsMonotone) (p : CancelPolicy) :
    between c.start c.target (c.cancelValue elapsed p) := by
  cases p with
  | snapToEnd => simpa [cancelValue] using between_right c.start c.target
  | hold => simpa [cancelValue] using c.sample_between elapsed hm

/-- A clip that shows `v` at every time. -/
def freeze (v : Rat) (easing : Easing := .linear) : Clip where
  start := v
  target := v
  duration := 0
  easing := easing

theorem freeze_const (v : Rat) (easing : Easing) (t : Rat) : (freeze v easing).sample t = v := by
  simp [freeze, sample, Anim.sample_nonpos_duration]

def cancel (c : Clip) (elapsed : Rat) : CancelPolicy → Clip
  | .snapToEnd => freeze c.target c.easing
  | .hold => freeze (c.sample elapsed) c.easing

/-- The clip produced by cancelling keeps that value at every later time. -/
theorem cancel_stable (c : Clip) (elapsed t : Rat) (p : CancelPolicy) :
    (c.cancel elapsed p).sample t = c.cancelValue elapsed p := by
  cases p <;> simp [cancel, cancelValue, freeze_const]

end Clip

/-! ## A shared clock -/

structure Clock where
  now : Rat
deriving Repr, Inhabited

namespace Clock

def advance (c : Clock) (dt : Rat) : Clock := ⟨c.now + dt⟩

def after : Clock → List Rat → Clock
  | c, [] => c
  | c, dt :: dts => (c.advance dt).after dts

theorem after_sum (c : Clock) (dts : List Rat) : (c.after dts).now = c.now + dts.sum := by
  induction dts generalizing c with
  | nil => simp [after, Rat.add_zero]
  | cons dt dts ih =>
    simp only [after, advance, List.sum_cons]
    rw [ih]
    grind

/-- Sample a clip that started at `origin` on this clock. -/
def playing (c : Clip) (origin : Rat) (clk : Clock) : Rat :=
  c.sample (clk.now - origin)

theorem playing_frame_independent (c : Clip) (origin : Rat) (clk : Clock) (a b : List Rat)
    (h : a.sum = b.sum) : playing c origin (clk.after a) = playing c origin (clk.after b) := by
  simp only [playing, after_sum, h]

end Clock

/-! ## Pixels

`toPixel` is half-up: `floor(x + 1/2)`. An integer rational is that integer, so a clip
that has reached an integer target is on that pixel, with no rounding left to do.
-/

def toPixel (x : Rat) : Int := (x + 1 / 2).floor

private theorem floor_half : ((1 : Rat) / 2).floor = 0 := by
  apply Int.le_antisymm
  · have : ((1 : Rat) / 2).floor < 1 := (Rat.floor_lt_iff).mpr (by grind)
    omega
  · exact (Rat.le_floor_iff).mpr (by grind : (0 : Rat) ≤ 1 / 2)

theorem toPixel_intCast (n : Int) : toPixel (n : Rat) = n := by
  unfold toPixel
  rw [Rat.add_comm, Rat.floor_add_intCast, floor_half, Int.zero_add]

theorem Clip.toPixel_at_end (c : Clip) (t : Rat) (h : c.duration ≤ t) :
    toPixel (c.sample t) = toPixel c.target := by
  rw [c.sample_ge_duration t h]

theorem Clip.toPixel_at_end_int (c : Clip) (t : Rat) (n : Int) (h : c.duration ≤ t)
    (ht : c.target = n) : toPixel (c.sample t) = n := by
  rw [c.toPixel_at_end t h, ht, toPixel_intCast]

/-- Clamp into `[0, 1]`, then the nearest byte `0..255` by the same half-up rule. -/
def unitClamp (x : Rat) : Rat := min 1 (max 0 x)

theorem unitClamp_zero : unitClamp 0 = 0 := by
  have h0 : (0 : Rat) ≤ 0 := Rat.le_refl
  have h1 : (0 : Rat) ≤ 1 := by grind
  simp [unitClamp, max_eq_right h0, min_eq_right h1]

theorem unitClamp_one : unitClamp 1 = 1 := by
  have h : (0 : Rat) ≤ 1 := by grind
  simp [unitClamp, max_eq_right h, min_eq_left (Rat.le_refl : (1 : Rat) ≤ 1)]

def toUnitByte (x : Rat) : Int := toPixel (unitClamp x * 255)

theorem toUnitByte_zero : toUnitByte 0 = 0 := by
  show toPixel (unitClamp 0 * 255) = 0
  rw [unitClamp_zero, Rat.zero_mul]
  exact toPixel_intCast 0

theorem toUnitByte_one : toUnitByte 1 = 255 := by
  show toPixel (unitClamp 1 * 255) = 255
  rw [unitClamp_one, Rat.one_mul]
  exact toPixel_intCast 255

theorem Clip.toUnitByte_at_end (c : Clip) (t : Rat) (h : c.duration ≤ t) :
    toUnitByte (c.sample t) = toUnitByte c.target := by
  rw [c.sample_ge_duration t h]

end UVL.Anim
