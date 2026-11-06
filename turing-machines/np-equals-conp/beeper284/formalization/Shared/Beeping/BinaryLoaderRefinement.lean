import Shared.Beeping.BinaryLoader

/-! The finite silent bootstrap is itself a progress-sensitive event
refinement. Its initial transitions belong to the first source segment. -/
namespace Shared.Beeping.BinaryLoader
open Shared.Beeping.Machines

variable {n : Nat} (M : Machine n) (bits : List Bool)

def shiftedBoundary (i : Nat) : Nat :=
  if i = 0 then 0 else 2 * count M.blank bits + i

theorem shifted_run (k : Nat) :
    (machine M bits).system.run (2 * count M.blank bits + k) =
      embed M bits ((loadedSystem M bits).run k) := by
  rw [EventSystem.run_add,run_eq_advance]
  change (machine M bits).system.advance
    ((machine M bits).system.advance (machine M bits).initial (2 * count M.blank bits)) k = _
  rw [boot_run,target_advance,← loaded_run]

theorem event_in_segment (i j : Nat) (hlo : shiftedBoundary M bits i ≤ j)
    (hhi : j < shiftedBoundary M bits (i + 1))
    (hb : (machine M bits).system.BeepAt j) : j = 2 * count M.blank bits + i := by
  have hj : 2 * count M.blank bits ≤ j := by
    by_contra hn
    exact boot_silent M bits j (by omega) hb
  cases i with
  | zero => simp [shiftedBoundary] at hlo hhi; omega
  | succ i => simp [shiftedBoundary] at hlo hhi; omega

/-- The loader cannot stall: after its fixed silent startup every source step
is simulated by exactly one target step. -/
def refinement : EventRefinement (loadedSystem M bits) (machine M bits).system where
  Rel := fun c d => (c = (loadedSystem M bits).initial ∧ d = (machine M bits).system.initial) ∨
    d = embed M bits c
  boundary := shiftedBoundary M bits
  boundary_zero := by simp [shiftedBoundary]
  progress := by
    intro i
    cases i with
    | zero => simp [shiftedBoundary]
    | succ i => simp [shiftedBoundary]
  related := by
    intro i
    cases i with
    | zero => left; simp [shiftedBoundary]
    | succ i => right; simpa [shiftedBoundary] using shifted_run M bits (i+1)
  event_iff := by
    intro i
    constructor
    · intro hb
      refine ⟨2 * count M.blank bits + i, ?_, ?_, (event_shift M bits i).2 hb⟩
      · cases i <;> simp [shiftedBoundary]
      · cases i <;> simp [shiftedBoundary]
    · rintro ⟨j,hlo,hhi,hb⟩
      have he := event_in_segment M bits i j hlo hhi hb
      subst j
      exact (event_shift M bits i).1 hb
  event_unique := by
    intro i j k hj hj' hk hk' hbj hbk
    have he := event_in_segment M bits i j hj hj' hbj
    have hf := event_in_segment M bits i k hk hk' hbk
    omega

end Shared.Beeping.BinaryLoader
