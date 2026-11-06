import Shared.Beeping.NPcoNP.Source284GraphFirstIteration

/-! Composes the finite reference-attempt setup with its first positive-clock
record lookup setup. This is a register-graph result, not a binary-tape or
whole bounded-evaluator refinement. -/
namespace Shared.Beeping.NPcoNP.Source284GraphReferenceFirstStep
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphReferenceAttempt
open Shared.Beeping.NPcoNP.Source284GraphFirstIteration

abbrev Bank := PASoundness.RegisterMachine.Bank 12

/-- A positive reference candidate counter and reference clock finish the
attempt setup and reach the first record-lookup setup in positive silent time.
The three zero scratch premises are those of the preceding setup theorem. -/
theorem reference_first_step (b : Bank) (h7 : 0 < b 7) (h5 : 0 < b 5)
    (h9 : b 9 = 0) (h10 : b 10 = 0) (h11 : b 11 = 0) :
    let d := ((7*(b 7-1)+b 8+5) + (b 1+b 2+7*b 5+6)) + (5*b 6+6)
    let r := ready b
    0 < d ∧ target.system.advance ⟨31,b⟩ d =
      ⟨60,bank r 0 (b 6) 0 (b 6) (b 5-1)⟩ ∧
      target.system.wordFrom ⟨31,b⟩ d = [] := by
  have ha := reference_attempt b h7 h9 h10 h11
  have hi := ready_first_iteration b h5 h9 h10
  dsimp only at ha hi ⊢
  refine ⟨by omega, ?_, ?_⟩
  · rw [WordEventSystem.advance_add, ha.2.1, hi.1]
  · rw [WordEventSystem.wordFrom_add, ha.2.1, ha.2.2, hi.2]
    rfl

end Shared.Beeping.NPcoNP.Source284GraphReferenceFirstStep
