import UVL.Anim.Basic

/-!
# Parallel, sequence, and stagger

A group is a list of clips with start offsets. Its duration is the latest finish
(`max(0, offset + duration)` over the members). At that time every member is at
its own target. Closed forms:

* `parallel` — every offset is `0`, so the duration is the longest clip.
* `sequence` — offsets are prefix sums. If every duration is `≥ 0`, the duration
  is the sum, and adjacent clips meet when one's target is the next one's start.
* `stagger` — item `i` starts at `i * delay`. If the delay is `≥ 0` and every
  clip has the same duration `d ≥ 0`, the duration is `(n - 1) * delay + d`.
-/

namespace UVL.Anim

structure Span where
  offset : Rat
  clip : Clip
deriving Repr, Inhabited

namespace Span

def finish (s : Span) : Rat := s.offset + s.clip.duration

def sample (s : Span) (groupT : Rat) : Rat := s.clip.sample (groupT - s.offset)

def shift (d : Rat) (s : Span) : Span := { s with offset := s.offset + d }

theorem shift_finish (d : Rat) (s : Span) : (shift d s).finish = s.finish + d := by
  simp [shift, finish]
  grind

/-- Once group time has reached this span's finish, the clip is exactly at its target. -/
theorem sample_ge_finish (s : Span) (t : Rat) (h : s.finish ≤ t) : s.sample t = s.clip.target := by
  have hle : s.clip.duration + s.offset ≤ t := by rw [Rat.add_comm]; exact h
  have hsub : s.clip.duration ≤ t - s.offset := (Rat.add_le_iff_le_sub).mp hle
  simpa [sample] using s.clip.sample_ge_duration (t - s.offset) hsub

/-- Reverse one member from its value at `groupT`. The new span starts at `groupT`. -/
def reverse (s : Span) (groupT : Rat) (dur : Rat := s.clip.duration) : Span where
  offset := groupT
  clip := s.clip.reverse (groupT - s.offset) dur

theorem reverse_continuous (s : Span) (groupT dur : Rat) (hd : 0 < dur) :
    (s.reverse groupT dur).sample groupT = s.sample groupT := by
  simp only [reverse, sample]
  have h0 : groupT - groupT = 0 := by grind
  rw [h0]
  exact s.clip.reverse_continuous (groupT - s.offset) dur hd

theorem reverse_ge_duration (s : Span) (groupT dur t : Rat) (h : dur ≤ t) :
    (s.reverse groupT dur).sample (groupT + t) = s.clip.start := by
  simp only [reverse, sample]
  have he : groupT + t - groupT = t := by grind
  rw [he]
  exact s.clip.reverse_ge_duration (groupT - s.offset) dur t h

end Span

/-- Latest finish, or `0` when there are no spans. -/
def total : List Span → Rat
  | [] => 0
  | s :: ss => max s.finish (total ss)

theorem total_nil : total [] = 0 := rfl

theorem le_total {spans : List Span} {s : Span} (h : s ∈ spans) : s.finish ≤ total spans := by
  induction h with
  | head =>
    simp only [total]
    exact le_max_left _ _
  | tail _ _ ih =>
    simp only [total]
    exact Rat.le_trans ih (le_max_right _ _)

/-- At or after `total spans`, every member is at its target. -/
theorem spans_done (spans : List Span) (t : Rat) (ht : total spans ≤ t) :
    ∀ s ∈ spans, s.sample t = s.clip.target := by
  intro s hs
  exact s.sample_ge_finish t (Rat.le_trans (le_total hs) ht)

theorem total_shift_eq (d : Rat) (spans : List Span) (hd : 0 ≤ d) (hf : ∀ s ∈ spans, 0 ≤ s.finish)
    (hne : spans ≠ []) : total (spans.map (Span.shift d)) = total spans + d := by
  induction spans with
  | nil => exact absurd rfl hne
  | cons s ss ih =>
    simp only [List.map_cons, total, Span.shift_finish]
    have hfss : ∀ x ∈ ss, 0 ≤ x.finish := fun x hx => hf x (List.mem_cons_of_mem _ hx)
    have hfs : 0 ≤ s.finish := hf s (List.mem_cons_self ..)
    by_cases hempty : ss = []
    · subst hempty
      simp [total]
      have hfd : 0 ≤ s.finish + d := Rat.add_nonneg hfs hd
      rw [max_eq_left hfd, max_eq_left hfs]
    · rw [ih hfss hempty, max_add]

def parallel (clips : List Clip) : List Span :=
  clips.map fun c => { offset := 0, clip := c }

def maxDur : List Clip → Rat
  | [] => 0
  | c :: cs => max c.duration (maxDur cs)

theorem parallel_duration (clips : List Clip) : total (parallel clips) = maxDur clips := by
  induction clips with
  | nil => simp [parallel, total, maxDur]
  | cons c cs ih =>
    simp only [parallel, List.map_cons, total]
    have hfin : Span.finish { offset := 0, clip := c } = c.duration := by simp [Span.finish, Rat.zero_add]
    rw [hfin, show total (cs.map fun c => { offset := 0, clip := c }) = maxDur cs from by
      simpa [parallel] using ih, maxDur]

def sumDur : List Clip → Rat
  | [] => 0
  | c :: cs => c.duration + sumDur cs

theorem sumDur_nonneg {clips : List Clip} (h : ∀ c ∈ clips, 0 ≤ c.duration) : 0 ≤ sumDur clips := by
  induction clips with
  | nil => exact Rat.le_refl
  | cons c cs ih =>
    exact Rat.add_nonneg (h c (List.mem_cons_self ..))
      (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

def sequence : List Clip → List Span
  | [] => []
  | c :: cs => { offset := 0, clip := c } :: (sequence cs).map (Span.shift c.duration)

theorem sequence_finish_nonneg {clips : List Clip} (h : ∀ c ∈ clips, 0 ≤ c.duration) :
    ∀ s ∈ sequence clips, 0 ≤ s.finish := by
  induction clips with
  | nil => intro s hs; cases hs
  | cons c cs ih =>
    intro s hs
    have hc : 0 ≤ c.duration := h c (List.mem_cons_self ..)
    have hcs : ∀ x ∈ cs, 0 ≤ x.duration := fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [sequence, List.mem_cons] at hs
    cases hs with
    | inl heq =>
      subst heq
      simpa [Span.finish, Rat.zero_add] using hc
    | inr hm =>
      obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hm
      have h0 : 0 ≤ s0.finish := ih hcs s0 hs0
      rw [Span.shift_finish]
      exact Rat.add_nonneg h0 hc

/-- With nonnegative durations, a sequence lasts exactly the sum of its clips. -/
theorem sequence_duration {clips : List Clip} (h : ∀ c ∈ clips, 0 ≤ c.duration) :
    total (sequence clips) = sumDur clips := by
  induction clips with
  | nil => simp [sequence, total, sumDur]
  | cons c cs ih =>
    have hc : 0 ≤ c.duration := h c (List.mem_cons_self ..)
    have hcs : ∀ x ∈ cs, 0 ≤ x.duration := fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [sequence, total, sumDur]
    by_cases hempty : cs = []
    · subst hempty
      simp [sequence, total, sumDur, Span.finish, Rat.zero_add, Rat.add_zero]
      exact max_eq_left hc
    · have hseq : sequence cs ≠ [] := by
        cases cs with
        | nil => exact absurd rfl hempty
        | cons _ _ => simp [sequence]
      rw [total_shift_eq c.duration (sequence cs) hc (sequence_finish_nonneg hcs) hseq, ih hcs]
      have hsum : 0 ≤ sumDur cs := sumDur_nonneg hcs
      have hle : c.duration ≤ c.duration + sumDur cs := le_add_of_nonneg_right hsum
      have hfin : Span.finish { offset := 0, clip := c } = c.duration := by
        simp [Span.finish, Rat.zero_add]
      rw [hfin, max_eq_right (by simpa [Rat.add_comm] using hle), Rat.add_comm]

theorem sequence_pair (c1 c2 : Clip) :
    sequence [c1, c2] = [{ offset := 0, clip := c1 }, { offset := c1.duration, clip := c2 }] := by
  simp [sequence, Span.shift, List.map, Rat.zero_add]

/-- At the first clip's duration, it is at its target and the next clip (if it has a positive
duration) is still at its start. That is the hand-off of a sequence. -/
theorem sequence_join (c1 c2 : Clip) (h2 : 0 < c2.duration) :
    (sequence [c1, c2])[0]!.sample c1.duration = c1.target ∧
      (sequence [c1, c2])[1]!.sample c1.duration = c2.start := by
  have hpair := sequence_pair c1 c2
  refine ⟨?_, ?_⟩
  · have h0 : (sequence [c1, c2])[0]! = { offset := 0, clip := c1 } := by simp [hpair]
    rw [h0]
    have hsub : c1.duration - 0 = c1.duration := by grind
    simpa [Span.sample, hsub] using c1.sample_ge_duration c1.duration (Rat.le_refl)
  · have h1 : (sequence [c1, c2])[1]! = { offset := c1.duration, clip := c2 } := by simp [hpair]
    rw [h1]
    have h0 : c1.duration - c1.duration = 0 := by grind
    have hs : c2.sample 0 = c2.start := c2.sample_le_zero 0 h2 (Rat.le_refl)
    simpa [Span.sample, h0] using hs

def stagger (delay : Rat) : List Clip → List Span
  | [] => []
  | c :: cs => { offset := 0, clip := c } :: (stagger delay cs).map (Span.shift delay)

theorem stagger_finish_nonneg {delay : Rat} {clips : List Clip}
    (hdelay : 0 ≤ delay) (h : ∀ c ∈ clips, 0 ≤ c.duration) :
    ∀ s ∈ stagger delay clips, 0 ≤ s.finish := by
  induction clips with
  | nil => intro s hs; cases hs
  | cons c cs ih =>
    intro s hs
    have hc : 0 ≤ c.duration := h c (List.mem_cons_self ..)
    have hcs : ∀ x ∈ cs, 0 ≤ x.duration := fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [stagger, List.mem_cons] at hs
    cases hs with
    | inl heq =>
      subst heq
      simpa [Span.finish, Rat.zero_add] using hc
    | inr hm =>
      obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hm
      rw [Span.shift_finish]
      exact Rat.add_nonneg (ih hcs s0 hs0) hdelay

theorem maxDur_const (clips : List Clip) (d : Rat) (hne : clips ≠ []) (h : ∀ c ∈ clips, c.duration = d)
    (hd : 0 ≤ d) : maxDur clips = d := by
  induction clips with
  | nil => exact absurd rfl hne
  | cons c cs ih =>
    have hc : c.duration = d := h c (List.mem_cons_self ..)
    simp only [maxDur, hc]
    cases cs with
    | nil =>
      simp [maxDur]
      exact max_eq_left hd
    | cons c2 rest =>
      have hcs : ∀ x ∈ c2 :: rest, x.duration = d := fun x hx =>
        h x (List.mem_cons_of_mem _ hx)
      rw [ih (by simp) hcs]
      exact max_eq_left (Rat.le_refl)

/-- `(n - 1) * delay + d` for `n > 0`, and `0` for an empty stagger. -/
def staggerDuration (delay d : Rat) (n : Nat) : Rat :=
  if n = 0 then 0 else ((n - 1 : Nat) : Rat) * delay + d

theorem staggerDuration_zero (delay d : Rat) : staggerDuration delay d 0 = 0 := by
  simp [staggerDuration]

theorem staggerDuration_succ (delay d : Rat) (n : Nat) :
    staggerDuration delay d (n + 1) = (n : Rat) * delay + d := by
  unfold staggerDuration
  have : ¬ n + 1 = 0 := Nat.succ_ne_zero n
  simp

/-- Equal durations and a nonnegative delay: the duration is `staggerDuration`. -/
theorem stagger_uniform (delay d : Rat) (clips : List Clip) (hdelay : 0 ≤ delay) (hd : 0 ≤ d)
    (h : ∀ c ∈ clips, c.duration = d) :
    total (stagger delay clips) = staggerDuration delay d clips.length := by
  induction clips with
  | nil => simp [stagger, total, staggerDuration]
  | cons c cs ih =>
    have hc : c.duration = d := h c (List.mem_cons_self ..)
    have hcs : ∀ x ∈ cs, x.duration = d := fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [stagger, total, List.length_cons]
    have hhead : Span.finish { offset := 0, clip := c } = d := by simp [Span.finish, Rat.zero_add, hc]
    cases cs with
    | nil =>
      simp [stagger, total, hhead, staggerDuration_succ, Rat.zero_mul, Rat.zero_add]
      exact max_eq_left hd
    | cons c2 rest =>
      have hcs' : ∀ x ∈ c2 :: rest, x.duration = d := hcs
      have hst : stagger delay (c2 :: rest) ≠ [] := by simp [stagger]
      have hnn : ∀ s ∈ stagger delay (c2 :: rest), 0 ≤ s.finish :=
        stagger_finish_nonneg hdelay fun x hx => by rw [hcs' x hx]; exact hd
      have ih' := ih hcs'
      rw [total_shift_eq delay (stagger delay (c2 :: rest)) hdelay hnn hst, ih', hhead,
        List.length_cons, staggerDuration_succ]
      have hcast : ((rest.length + 1 : Nat) : Rat) = (rest.length : Rat) + 1 := by
        simp
      have hgrow : (rest.length : Rat) * delay + d + delay =
          ((rest.length + 1 : Nat) : Rat) * delay + d := by
        rw [hcast]; grind
      rw [hgrow, staggerDuration_succ]
      exact max_eq_right (by
        rw [Rat.add_comm]
        exact le_add_of_nonneg_right
          (Rat.mul_nonneg (show 0 ≤ ((rest.length + 1 : Nat) : Rat) from Rat.natCast_nonneg) hdelay))

inductive Group where
  | parallel (clips : List Clip)
  | sequence (clips : List Clip)
  | stagger (delay : Rat) (clips : List Clip)
deriving Repr

namespace Group

def spans : Group → List Span
  | .parallel cs => Anim.parallel cs
  | .sequence cs => Anim.sequence cs
  | .stagger delay cs => Anim.stagger delay cs

def duration (g : Group) : Rat := total g.spans

/-- At the group's computed duration, every member is at its final value. -/
theorem done (g : Group) (t : Rat) (ht : g.duration ≤ t) :
    ∀ s ∈ g.spans, s.sample t = s.clip.target :=
  spans_done g.spans t ht

theorem parallel_duration (clips : List Clip) : (Group.parallel clips).duration = maxDur clips := by
  simp [duration, spans, Anim.parallel_duration]

theorem sequence_duration {clips : List Clip} (h : ∀ c ∈ clips, 0 ≤ c.duration) :
    (Group.sequence clips).duration = sumDur clips := by
  simp [duration, spans, Anim.sequence_duration h]

theorem stagger_uniform (delay d : Rat) (clips : List Clip) (hdelay : 0 ≤ delay) (hd : 0 ≤ d)
    (h : ∀ c ∈ clips, c.duration = d) :
    (Group.stagger delay clips).duration = staggerDuration delay d clips.length := by
  simp [duration, spans, Anim.stagger_uniform delay d clips hdelay hd h]

/-- Parallel clips that share one duration finish together, on that duration. -/
theorem parallel_sync (clips : List Clip) (d : Rat) (hne : clips ≠ [])
    (h : ∀ c ∈ clips, c.duration = d) (hd : 0 ≤ d) :
    (Group.parallel clips).duration = d ∧
      ∀ t, d ≤ t → ∀ c ∈ clips, c.sample t = c.target := by
  refine ⟨?_, ?_⟩
  · rw [parallel_duration, maxDur_const clips d hne h hd]
  · intro t ht c hc
    exact c.sample_ge_duration t (by rw [h c hc]; exact ht)

end Group

end UVL.Anim
