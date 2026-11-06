import Shared.Beeping.Events

/-!
Run-level, event-preserving stuttering refinement. The target segment for
source transition `i` is the half-open interval `[boundary i, boundary (i+1))`.
Boundaries are strictly increasing and start at zero. The matching conditions
allow a beep anywhere in the segment and require exactly one when the source
beeps; silent source transitions have no target beeps in their segment.

A concrete compiler must construct such a refinement, including the relation
and all boundary/progress witnesses. This structure is not that compiler.
-/
namespace Shared.Beeping

structure EventRefinement {S T : Type} (source : EventSystem S) (target : EventSystem T) where
  Rel : S → T → Prop
  boundary : Nat → Nat
  boundary_zero : boundary 0 = 0
  progress : ∀ i, boundary i < boundary (i + 1)
  related : ∀ i, Rel (source.run i) (target.run (boundary i))
  event_iff : ∀ i, source.BeepAt i ↔
    ∃ j, boundary i ≤ j ∧ j < boundary (i + 1) ∧ target.BeepAt j
  event_unique : ∀ i j k, boundary i ≤ j → j < boundary (i + 1) →
    boundary i ≤ k → k < boundary (i + 1) → target.BeepAt j → target.BeepAt k → j = k

namespace EventRefinement

variable {S T : Type} {source : EventSystem S} {target : EventSystem T}
variable (r : EventRefinement source target)

theorem initial_related : r.Rel source.initial target.initial := by
  have h := r.related 0
  simpa [r.boundary_zero] using h

theorem boundary_mono {i j : Nat} (h : i ≤ j) : r.boundary i ≤ r.boundary j := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step j _ ih =>
    have hp : r.boundary j < r.boundary (Nat.succ j) := by simpa using r.progress j
    exact Nat.le_trans ih (Nat.le_of_lt hp)

theorem boundary_strict {i j : Nat} (h : i < j) : r.boundary i < r.boundary j := by
  have hm : r.boundary (i + 1) ≤ r.boundary j := r.boundary_mono (by omega)
  exact Nat.lt_of_lt_of_le (r.progress i) hm

theorem boundary_ge (i : Nat) : i ≤ r.boundary i := by
  induction i with
  | zero => omega
  | succ i ih =>
    have hp := r.progress i
    omega

/-- Each target transition belongs to a finite positive source segment. -/
theorem covers (t : Nat) :
    ∃ i, r.boundary i ≤ t ∧ t < r.boundary (i + 1) := by
  induction t with
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · simp [r.boundary_zero]
    · have hp := r.progress 0
      rw [r.boundary_zero] at hp
      simpa using hp
  | succ t ih =>
    obtain ⟨i, hlo, hhi⟩ := ih
    by_cases h : t + 1 < r.boundary (i + 1)
    · exact ⟨i, by omega, h⟩
    · have hp := r.progress (i + 1)
      exact ⟨i + 1, by omega, by omega⟩

/-- The covering segment is unique. -/
theorem segment_unique {i j t : Nat}
    (hi₁ : r.boundary i ≤ t) (hi₂ : t < r.boundary (i + 1))
    (hj₁ : r.boundary j ≤ t) (hj₂ : t < r.boundary (j + 1)) : i = j := by
  by_cases h : i < j
  · have hm := r.boundary_mono (show i + 1 ≤ j by omega)
    omega
  · by_cases h' : j < i
    · have hm := r.boundary_mono (show j + 1 ≤ i by omega)
      omega
    · omega

/-- The boundary embedding is cofinal, ruling out an infinite target stall
within finitely many source segments. -/
theorem boundaries_unbounded (t : Nat) : ∃ i, t < r.boundary i := by
  refine ⟨t + 1, ?_⟩
  have h := r.boundary_ge (t + 1)
  omega

theorem eventuallySilent_iff (r : EventRefinement source target) : source.EventuallySilent ↔ target.EventuallySilent := by
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨r.boundary T, ?_⟩
    intro t ht hb
    obtain ⟨i, hlo, hhi⟩ := r.covers t
    have hi : T ≤ i := by
      by_cases h : i < T
      · have hm := r.boundary_mono (show i + 1 ≤ T by omega)
        omega
      · omega
    exact hT i hi ((r.event_iff i).2 ⟨t, hlo, hhi, hb⟩)
  · rintro ⟨T, hT⟩
    refine ⟨T, ?_⟩
    intro i hi hb
    obtain ⟨t, hlo, hhi, he⟩ := (r.event_iff i).1 hb
    have hg := r.boundary_ge i
    exact hT t (by omega) he

/-- A transition lying between two boundaries belongs to a segment whose
source index lies in the corresponding interval. -/
theorem covers_between {lo hi t : Nat}
    (hlo : r.boundary lo ≤ t) (hhi : t < r.boundary hi) :
    ∃ i, lo ≤ i ∧ i < hi ∧ r.boundary i ≤ t ∧ t < r.boundary (i + 1) := by
  obtain ⟨i, h₁, h₂⟩ := r.covers t
  have hli : lo ≤ i := by
    by_cases h : i < lo
    · have hm := r.boundary_mono (show i + 1 ≤ lo by omega)
      omega
    · omega
  have hih : i < hi := by
    by_cases h : hi ≤ i
    · have hm := r.boundary_mono h
      omega
    · omega
  exact ⟨i, hli, hih, h₁, h₂⟩

/-- Compose refinements without changing the observed event word. -/
def trans {U : Type} {middle : EventSystem T} {last : EventSystem U}
    (r₁ : EventRefinement source middle) (r₂ : EventRefinement middle last) :
    EventRefinement source last where
  Rel := fun s u => ∃ m, r₁.Rel s m ∧ r₂.Rel m u
  boundary := fun i => r₂.boundary (r₁.boundary i)
  boundary_zero := by rw [r₁.boundary_zero, r₂.boundary_zero]
  progress := fun i => r₂.boundary_strict (r₁.progress i)
  related := fun i => ⟨middle.run (r₁.boundary i), r₁.related i, r₂.related (r₁.boundary i)⟩
  event_iff := by
    intro i
    constructor
    · intro hs
      obtain ⟨j, hjlo, hjhi, hj⟩ := (r₁.event_iff i).1 hs
      obtain ⟨k, hklo, hkhi, hk⟩ := (r₂.event_iff j).1 hj
      have hmlo := r₂.boundary_mono hjlo
      have hmhi := r₂.boundary_mono (show j + 1 ≤ r₁.boundary (i + 1) by omega)
      exact ⟨k, by omega, by omega, hk⟩
    · rintro ⟨k, hklo, hkhi, hk⟩
      obtain ⟨j, hjlo, hjhi, hkjlo, hkjhi⟩ := r₂.covers_between hklo hkhi
      exact (r₁.event_iff i).2 ⟨j, hjlo, hjhi, (r₂.event_iff j).2 ⟨k, hkjlo, hkjhi, hk⟩⟩
  event_unique := by
    intro i k l hklo hkhi hllo hlhi hk hl
    obtain ⟨j, hjlo, hjhi, hkjlo, hkjhi⟩ := r₂.covers_between hklo hkhi
    obtain ⟨j', hj'lo, hj'hi, hljlo, hljhi⟩ := r₂.covers_between hllo hlhi
    have hj := (r₂.event_iff j).2 ⟨k, hkjlo, hkjhi, hk⟩
    have hj' := (r₂.event_iff j').2 ⟨l, hljlo, hljhi, hl⟩
    have heq := r₁.event_unique i j j' hjlo hjhi hj'lo hj'hi hj hj'
    subst j'
    exact r₂.event_unique j k l hkjlo hkjhi hljlo hljhi hk hl

/-- The identity refinement has one target transition per source step. -/
def refl (M : EventSystem S) : EventRefinement M M where
  Rel := Eq
  boundary := id
  boundary_zero := rfl
  progress := fun i => Nat.lt_succ_self i
  related := fun _ => rfl
  event_iff := by
    intro i
    constructor
    · intro h
      exact ⟨i, by simp, by simp, h⟩
    · rintro ⟨j, hlo, hhi, hj⟩
      have heq : j = i := by simp only [id_eq] at hlo hhi; omega
      simpa [heq] using hj
  event_unique := by
    intro i j k hjlo hjhi hklo hkhi _ _
    simp only [id_eq] at hjlo hjhi hklo hkhi
    omega

end EventRefinement

namespace EventSystem

def InfinitelyManyBeeps (M : EventSystem S) : Prop :=
  ∀ T, ∃ t, T ≤ t ∧ M.BeepAt t

theorem not_eventuallySilent_iff_infinitelyMany (M : EventSystem S) :
    ¬ M.EventuallySilent ↔ M.InfinitelyManyBeeps := by
  constructor
  · intro h T
    apply Classical.byContradiction
    intro hn
    apply h
    refine ⟨T, ?_⟩
    intro t ht hb
    exact hn ⟨t, ht, hb⟩
  · intro h hs
    obtain ⟨T, hT⟩ := hs
    obtain ⟨t, ht, hb⟩ := h T
    exact hT t ht hb

end EventSystem

namespace EventRefinement

variable {S T : Type} {source : EventSystem S} {target : EventSystem T}

theorem infinitelyManyBeeps_iff (r : EventRefinement source target) :
    source.InfinitelyManyBeeps ↔ target.InfinitelyManyBeeps := by
  rw [← EventSystem.not_eventuallySilent_iff_infinitelyMany,
      ← EventSystem.not_eventuallySilent_iff_infinitelyMany, r.eventuallySilent_iff]

end EventRefinement

namespace EventSystem

/-- Execute a finite number of transitions from an arbitrary configuration. -/
def advance (M : EventSystem S) (c : S) : Nat → S
  | 0 => c
  | k + 1 => (M.step (M.advance c k)).1

def BeepFrom (M : EventSystem S) (c : S) (k : Nat) : Prop :=
  (M.step (M.advance c k)).2 = true

theorem run_add (M : EventSystem S) (t k : Nat) :
    M.run (t + k) = M.advance (M.run t) k := by
  induction k with
  | zero => simp [advance]
  | succ k ih =>
    simp only [Nat.add_succ, EventSystem.run_succ, advance, ih]

theorem beepAt_add_iff (M : EventSystem S) (t k : Nat) :
    M.BeepAt (t + k) ↔ M.BeepFrom (M.run t) k := by
  simp only [BeepAt, BeepFrom, run_add]

end EventSystem

/-- Local simulation obligations. The duration function must be supplied;
its computability and cost are separate obligations of a concrete compiler. -/
structure SegmentSimulation {S T : Type} (source : EventSystem S) (target : EventSystem T) where
  Rel : S → T → Prop
  initial : Rel source.initial target.initial
  duration : S → T → Nat
  positive : ∀ s t, Rel s t → 0 < duration s t
  next : ∀ s t, Rel s t →
    Rel (source.step s).1 (target.advance t (duration s t))
  event_iff : ∀ s t, Rel s t →
    ((source.step s).2 = true ↔
      ∃ j, j < duration s t ∧ target.BeepFrom t j)
  event_unique : ∀ s t, Rel s t → ∀ j k,
    j < duration s t → k < duration s t →
      target.BeepFrom t j → target.BeepFrom t k → j = k

namespace SegmentSimulation

variable {S T : Type} {source : EventSystem S} {target : EventSystem T}
variable (s : SegmentSimulation source target)

def boundary : Nat → Nat
  | 0 => 0
  | i + 1 =>
      let b := boundary i
      b + s.duration (source.run i) (target.run b)

theorem related_boundary (i : Nat) :
    s.Rel (source.run i) (target.run (s.boundary i)) := by
  induction i with
  | zero => simpa [boundary] using s.initial
  | succ i ih =>
    have hn := s.next (source.run i) (target.run (s.boundary i)) ih
    change s.Rel (source.step (source.run i)).1
      (target.run (s.boundary i + s.duration (source.run i) (target.run (s.boundary i))))
    rw [EventSystem.run_add]
    exact hn

theorem boundary_progress (i : Nat) : s.boundary i < s.boundary (i + 1) := by
  have hp := s.positive (source.run i) (target.run (s.boundary i)) (s.related_boundary i)
  change s.boundary i < s.boundary i + s.duration (source.run i) (target.run (s.boundary i))
  omega

/-- Local matching and strictly positive durations give the global refinement. -/
def toEventRefinement : EventRefinement source target where
  Rel := s.Rel
  boundary := s.boundary
  boundary_zero := rfl
  progress := s.boundary_progress
  related := s.related_boundary
  event_iff := by
    intro i
    have hr := s.related_boundary i
    have hm := s.event_iff (source.run i) (target.run (s.boundary i)) hr
    change ((source.step (source.run i)).2 = true ↔ _)
    constructor
    · intro he
      obtain ⟨j, hj, hb⟩ := hm.1 he
      refine ⟨s.boundary i + j, by omega, ?_, ?_⟩
      · change s.boundary i + j < s.boundary i + s.duration (source.run i) (target.run (s.boundary i))
        omega
      · exact (target.beepAt_add_iff (s.boundary i) j).2 hb
    · rintro ⟨j, hjlo, hjhi, hb⟩
      let k := j - s.boundary i
      have hsum : s.boundary i + k = j := by dsimp [k]; omega
      have hk : k < s.duration (source.run i) (target.run (s.boundary i)) := by
        change j < s.boundary i + s.duration (source.run i) (target.run (s.boundary i)) at hjhi
        omega
      apply hm.2
      refine ⟨k, hk, ?_⟩
      apply (target.beepAt_add_iff (s.boundary i) k).1
      simpa [hsum] using hb
  event_unique := by
    intro i j k hjlo hjhi hklo hkhi hj hk
    let j' := j - s.boundary i
    let k' := k - s.boundary i
    have hjsum : s.boundary i + j' = j := by dsimp [j']; omega
    have hksum : s.boundary i + k' = k := by dsimp [k']; omega
    have hj' : j' < s.duration (source.run i) (target.run (s.boundary i)) := by
      change j < s.boundary i + s.duration (source.run i) (target.run (s.boundary i)) at hjhi
      omega
    have hk' : k' < s.duration (source.run i) (target.run (s.boundary i)) := by
      change k < s.boundary i + s.duration (source.run i) (target.run (s.boundary i)) at hkhi
      omega
    have hjb : target.BeepFrom (target.run (s.boundary i)) j' := by
      apply (target.beepAt_add_iff (s.boundary i) j').1
      simpa [hjsum] using hj
    have hkb : target.BeepFrom (target.run (s.boundary i)) k' := by
      apply (target.beepAt_add_iff (s.boundary i) k').1
      simpa [hksum] using hk
    have he := s.event_unique (source.run i) (target.run (s.boundary i))
      (s.related_boundary i) j' k' hj' hk' hjb hkb
    omega

end SegmentSimulation
end Shared.Beeping
