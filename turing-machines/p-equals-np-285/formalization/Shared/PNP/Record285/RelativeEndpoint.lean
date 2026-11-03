import Shared.PNP.Record285.RelativeTape
import Shared.PNP.Record285.SourceEndpoint

/-! Bridge the source event theorem to bounded executions of the full relative
tape machine. Canonical complexity and the physical 285-state table remain open. -/
namespace Shared.PNP.Record285.RelativeEndpoint
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.RelativeTape

/-- The candidate decides the bounded reference predicate on every canonical
input. No polynomial simulation claim is made here. -/
def RelativeGood (program exponent : Nat) : Prop :=
  ∀ n remaining, remaining < 2^n →
    ((∃ branch, branch < 2^n ∧
        relativeRun (2^n+remaining) n (initialRelative 0 branch) = none) ↔
      relativeRun program ((n+2)^exponent)
        (initialRelative (frame (2^n) remaining) 0) = none)

theorem comparison_iff (program exponent n radix remaining : Nat) :
    mismatch program exponent n radix remaining = false ↔
      ((∃ branch, branch < radix ∧
        relativeRun (radix+remaining) n (initialRelative 0 branch) = none) ↔
      relativeRun program ((n+2)^exponent)
        (initialRelative (frame radix remaining) 0) = none) := by
  have heq : mismatch program exponent n radix remaining = false ↔
      reference n radix remaining = candidate program exponent n radix remaining := by
    cases h₁ : reference n radix remaining <;>
      cases h₂ : candidate program exponent n radix remaining <;>
      simp [mismatch, h₁, h₂]
  rw [heq, Bool.eq_iff_iff, reference_halts_iff, candidate_halts_iff]

theorem goodCandidate_iff_relativeGood (program exponent : Nat) :
    GoodCandidate program exponent ↔ RelativeGood program exponent := by
  constructor
  · intro h n remaining hbound
    exact (comparison_iff program exponent n (2^n) remaining).1 (h n remaining hbound)
  · intro h n remaining hbound
    exact (comparison_iff program exponent n (2^n) remaining).2 (h n remaining hbound)

/-- Finite source events correspond exactly to a positive-exponent relative
candidate deciding the bounded reference predicate. -/
theorem finiteEvents_iff_relativeGood :
    controller.FiniteEventTimes ↔
      ∃ program exponent, 0 < exponent ∧ RelativeGood program exponent := by
  rw [finiteEvents_iff_goodCandidate]
  simp only [goodCandidate_iff_relativeGood]

theorem infinitelyMany_iff_no_relativeGood :
    controller.InfinitelyManyBeeps ↔
      ¬ ∃ program exponent, 0 < exponent ∧ RelativeGood program exponent := by
  rw [infinitelyMany_iff_no_goodCandidate]
  simp only [goodCandidate_iff_relativeGood]

end Shared.PNP.Record285.RelativeEndpoint
