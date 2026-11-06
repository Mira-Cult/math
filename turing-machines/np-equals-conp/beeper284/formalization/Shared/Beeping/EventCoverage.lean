import Shared.Beeping.Refinement

/-! Progress-sensitive event coverage permits a finite nonzero number of
target events per source event. It preserves eventual silence, but does not
claim to preserve event counts or ordered words. -/
namespace Shared.Beeping

structure EventCoverage {S T : Type} (source : EventSystem S) (target : EventSystem T) where
  boundary : Nat → Nat
  boundary_zero : boundary 0 = 0
  progress : ∀ i, boundary i < boundary (i+1)
  event_iff : ∀ i, source.BeepAt i ↔
    ∃ t, boundary i ≤ t ∧ t < boundary (i+1) ∧ target.BeepAt t

namespace EventCoverage
variable {S T : Type} {source : EventSystem S} {target : EventSystem T} (r : EventCoverage source target)

theorem boundary_mono {i j : Nat} (h : i ≤ j) : r.boundary i ≤ r.boundary j := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step j _ ih => exact Nat.le_trans ih (Nat.le_of_lt (r.progress j))

theorem boundary_ge (i : Nat) : i ≤ r.boundary i := by
  induction i with
  | zero => omega
  | succ i ih => have hp := r.progress i; omega

theorem covers (t : Nat) : ∃ i, r.boundary i ≤ t ∧ t < r.boundary (i+1) := by
  induction t with
  | zero =>
    refine ⟨0,?_,?_⟩
    · simp [r.boundary_zero]
    · have hp := r.progress 0
      rw [r.boundary_zero] at hp
      simpa using hp
  | succ t ih =>
    obtain ⟨i,hlo,hhi⟩ := ih
    by_cases h : t+1 < r.boundary (i+1)
    · exact ⟨i,by omega,h⟩
    · have hp := r.progress (i+1)
      exact ⟨i+1,by omega,by omega⟩

/-- Every target transition lies in a finite source segment; arbitrary
finite event duplication cannot change eventual silence. -/
theorem eventuallySilent_iff (r : EventCoverage source target) : source.EventuallySilent ↔ target.EventuallySilent := by
  constructor
  · rintro ⟨T,hT⟩
    refine ⟨r.boundary T,?_⟩
    intro t ht hb
    obtain ⟨i,hlo,hhi⟩ := r.covers t
    have hi : T ≤ i := by
      by_cases h : i < T
      · have hm := r.boundary_mono (show i+1 ≤ T by omega)
        omega
      · omega
    exact hT i hi ((r.event_iff i).2 ⟨t,hlo,hhi,hb⟩)
  · rintro ⟨T,hT⟩
    refine ⟨T,?_⟩
    intro i hi hb
    obtain ⟨t,hlo,_,he⟩ := (r.event_iff i).1 hb
    have hg := r.boundary_ge i
    exact hT t (by omega) he

theorem infinitelyManyBeeps_iff (r : EventCoverage source target) : source.InfinitelyManyBeeps ↔ target.InfinitelyManyBeeps := by
  rw [← EventSystem.not_eventuallySilent_iff_infinitelyMany,
      ← EventSystem.not_eventuallySilent_iff_infinitelyMany,r.eventuallySilent_iff]

/-- Exact-one refinements are a special case. -/
def ofRefinement (s : EventRefinement source target) : EventCoverage source target where
  boundary := s.boundary
  boundary_zero := s.boundary_zero
  progress := s.progress
  event_iff := s.event_iff

end EventCoverage
end Shared.Beeping
