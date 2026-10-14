/-!
# Box constraints

Flutter-style box constraints (`Constraints → Size`), over natural-number
logical pixels so that the layout invariants can be stated and proved.

The key guarantee: `constrain` always produces a size the constraints admit
(`constrain_admits`), and every layout result carries such a proof in its type.
-/

namespace UViz.Layout

structure Size where
  w : Nat
  h : Nat
deriving Inhabited, Repr, BEq, DecidableEq

structure Constraints where
  minW : Nat
  maxW : Nat
  minH : Nat
  maxH : Nat
  hw : minW ≤ maxW := by omega
  hh : minH ≤ maxH := by omega

namespace Constraints

instance : Repr Constraints where
  reprPrec c _ := s!"Constraints(w: {c.minW}..{c.maxW}, h: {c.minH}..{c.maxH})"

/-- `c.Admits s` : the size `s` respects every bound of `c`. -/
def Admits (c : Constraints) (s : Size) : Prop :=
  c.minW ≤ s.w ∧ s.w ≤ c.maxW ∧ c.minH ≤ s.h ∧ s.h ≤ c.maxH

instance (c : Constraints) (s : Size) : Decidable (c.Admits s) := by
  unfold Admits; exact inferInstance

def tight (s : Size) : Constraints := ⟨s.w, s.w, s.h, s.h, Nat.le_refl _, Nat.le_refl _⟩
def loose (s : Size) : Constraints := ⟨0, s.w, 0, s.h, Nat.zero_le _, Nat.zero_le _⟩

/-- Same maxima, minima dropped. -/
def loosen (c : Constraints) : Constraints := ⟨0, c.maxW, 0, c.maxH, Nat.zero_le _, Nat.zero_le _⟩

/-- Clamp `x` into `[lo, hi]`. -/
@[inline] def clampN (lo hi x : Nat) : Nat := Min.min hi (Max.max lo x)

theorem clampN_ge {lo hi x : Nat} (h : lo ≤ hi) : lo ≤ clampN lo hi x := by
  unfold clampN; omega
theorem clampN_le {lo hi x : Nat} : clampN lo hi x ≤ hi := by
  unfold clampN; omega

/-- The closest admitted size to `s`. -/
def constrain (c : Constraints) (s : Size) : Size :=
  ⟨clampN c.minW c.maxW s.w, clampN c.minH c.maxH s.h⟩

/-- **Invariant**: `constrain` never produces a size outside the constraints. -/
theorem constrain_admits (c : Constraints) (s : Size) : c.Admits (c.constrain s) :=
  ⟨clampN_ge c.hw, clampN_le, clampN_ge c.hh, clampN_le⟩

/-- `constrain` is the identity on admitted sizes. -/
theorem constrain_of_admits {c : Constraints} {s : Size} (h : c.Admits s) : c.constrain s = s := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases s with
  | mk sw sh =>
    simp only at h1 h2 h3 h4
    simp only [constrain, clampN, Size.mk.injEq]
    omega

/-- The biggest admitted size. -/
def biggest (c : Constraints) : Size := ⟨c.maxW, c.maxH⟩
theorem biggest_admits (c : Constraints) : c.Admits c.biggest :=
  ⟨c.hw, Nat.le_refl _, c.hh, Nat.le_refl _⟩

/-- Shrink both bounds by `dw`/`dh` (used by padding). -/
def deflate (c : Constraints) (dw dh : Nat) : Constraints :=
  ⟨c.minW - dw, c.maxW - dw, c.minH - dh, c.maxH - dh,
   Nat.sub_le_sub_right c.hw _, Nat.sub_le_sub_right c.hh _⟩

/-- Child constraints with the requested bounds, capped by `c`'s maxima
(minima may be looser than `c`'s, e.g. for centering). -/
def within (c : Constraints) (minW maxW minH maxH : Nat) : Constraints :=
  ⟨Min.min (Min.min c.maxW maxW) minW, Min.min c.maxW maxW,
   Min.min (Min.min c.maxH maxH) minH, Min.min c.maxH maxH,
   Nat.min_le_left _ _, Nat.min_le_left _ _⟩

theorem within_maxW (c : Constraints) (a b d e : Nat) : (c.within a b d e).maxW ≤ c.maxW :=
  Nat.min_le_left _ _
theorem within_maxH (c : Constraints) (a b d e : Nat) : (c.within a b d e).maxH ≤ c.maxH :=
  Nat.min_le_left _ _

/-- Anything admitted by `c.within …` respects `c`'s maxima. -/
theorem le_max_of_within {c : Constraints} {a b d e : Nat} {s : Size}
    (h : (c.within a b d e).Admits s) : s.w ≤ c.maxW ∧ s.h ≤ c.maxH :=
  ⟨Nat.le_trans h.2.1 (c.within_maxW a b d e), Nat.le_trans h.2.2.2 (c.within_maxH a b d e)⟩

/-- Tighten the given dimensions (clamped into `c`); keep the others. -/
def tighten (c : Constraints) (w h : Option Nat) : Constraints :=
  let tw := w.map (clampN c.minW c.maxW)
  let th := h.map (clampN c.minH c.maxH)
  match tw, th with
  | some a, some b => c.within a a b b
  | some a, none => c.within a a c.minH c.maxH
  | none, some b => c.within c.minW c.maxW b b
  | none, none => c

/-- Sizes admitted by the tightened constraints are admitted by `c`. -/
theorem admits_of_tighten {c : Constraints} {w h : Option Nat} {s : Size}
    (hs : (c.tighten w h).Admits s) : c.Admits s := by
  have hw := c.hw; have hh := c.hh
  unfold tighten at hs
  cases w <;> cases h <;>
    simp only [Option.map, within, Admits, clampN] at hs ⊢ <;> omega

end Constraints

/-- A size together with the proof that it satisfies `c`. -/
abbrev Fitted (c : Constraints) := { s : Size // c.Admits s }

end UViz.Layout
