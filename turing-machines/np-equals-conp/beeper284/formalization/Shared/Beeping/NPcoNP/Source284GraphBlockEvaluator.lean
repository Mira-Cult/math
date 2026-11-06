import Shared.Beeping.NPcoNP.Source284GraphBlockApply

/-! The bounded reference evaluator remains in its checked graph block.
This discharges the operational premise of the candidate-block mirror. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphBlockEvaluator
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyRow (regs)
open Shared.Beeping.NPcoNP.Source284GraphRowStep (regs_eq_bank ordinal stepCost)
open Shared.Beeping.NPcoNP.Source284GraphEvaluator (tickCost evalCost)
open Shared.Beeping.NPcoNP.Source284GraphBlockSafety
open Shared.Beeping.NPcoNP.Source284Relative
abbrev Bank := PASoundness.RegisterMachine.Bank 12

theorem row_step (b : Bank) (description clock : Nat) (c : Source284Relative.Config)
    (hstate : c.state ≠ 0) :
    SafeSeg ⟨60,regs b c.left (c.right/2) (ordinal c) description 0 description clock⟩
      ⟨50,regs b (Source284Relative.step description c).left
        (Source284Relative.step description c).right
        (Source284Relative.step description c).state description 0 0 clock⟩
      (stepCost description c) := by
  let o := ordinal c
  let row := record description o
  let base := write (write b 8 c.left) 1 (c.right/2)
  have hl : SafeSeg ⟨60,regs b c.left (c.right/2) o description 0 description clock⟩
      ⟨68,regs b c.left (c.right/2) row description 0 0 clock⟩
      (Source284GraphSkip.lookupCost description o) := by
    simpa only [regs_eq_bank,row,base] using Source284GraphBlockLookup.lookup base o description clock
  have ha := Source284GraphBlockApply.apply b c.left (c.right/2) row description clock
  have hs := (cat hl ha).2
  refine ⟨(Source284GraphRowStep.row_step b description clock c hstate).2,?_⟩
  simpa only [stepCost,row,o] using hs

theorem accepting_tick (b : Bank) (l r d t : Nat) :
    SafeSeg ⟨50,regs b l r 0 d 0 0 (t+1)⟩ ⟨50,regs b l r 0 d 0 0 t⟩ 2 := by
  have h₁ := one _ _ (Source284GraphPrepStep.row50 b l r 0 d 0 0 t) (by simp [Inside])
  have h₂ := one _ _ (Source284GraphEvaluator.row51_zero b l r d 0 0 t) (by simp [Inside])
  simpa using cat h₁ h₂

theorem tick (b : Bank) (description remaining : Nat) (c : Source284Relative.Config) :
    SafeSeg ⟨50,regs b c.left c.right c.state description 0 0 (remaining+1)⟩
      ⟨50,regs b (Source284Relative.step description c).left
        (Source284Relative.step description c).right
        (Source284Relative.step description c).state description 0 0 remaining⟩
      (tickCost description c) := by
  by_cases hz : c.state=0
  · have he : Source284Relative.step description c = c := step_absorbing description c hz
    simp only [tickCost,hz,if_true,he]
    simpa [hz] using accepting_tick b c.left c.right description remaining
  · have ht : c.state-1+1=c.state := by omega
    have hp := Source284GraphBlockPrep.prepare b c.left c.right (c.state-1) description remaining
    have hp' : SafeSeg ⟨50,regs b c.left c.right c.state description 0 0 (remaining+1)⟩
        ⟨60,regs b c.left (c.right/2) (ordinal c) description 0 description remaining⟩
        (Source284GraphPrepStep.prepareCost description c.right) := by
      simpa only [ht,ordinal] using hp
    have hr := row_step b description remaining c hz
    simpa only [tickCost,hz,if_false] using cat hp' hr

/-- Every intermediate graph PC in a bounded evaluator run remains in the
reference block. In particular no silent excursion through an unrelated phase
can substitute for completion of a source tick. -/
theorem evaluate (b : Bank) (description : Nat) (c : Source284Relative.Config) (clock : Nat) :
    SafeSeg ⟨50,regs b c.left c.right c.state description 0 0 clock⟩
      ⟨50,regs b (Source284Relative.run description c clock).left
        (Source284Relative.run description c clock).right
        (Source284Relative.run description c clock).state description 0 0 0⟩
      (evalCost description c clock) := by
  induction clock generalizing c with
  | zero => simpa [evalCost] using zero ⟨50,regs b c.left c.right c.state description 0 0 0⟩
  | succ clock ih =>
    have ht := tick b description clock c
    have hi := ih (Source284Relative.step description c)
    have hr : Source284Relative.run description c (clock+1) =
        Source284Relative.run description (Source284Relative.step description c) clock := by
      rw [show clock+1=1+clock by omega,run_add_clock]
      rfl
    rw [evalCost,hr]
    exact cat ht hi

/-- The previously conditional block-mirror theorem now holds for every
finite source clock, with no residence hypothesis. -/
theorem candidate_evaluate (b : Bank) (description clock : Nat) (c : Source284Relative.Config) :
    target.system.advance
      (Source284GraphCandidateMirror.mapCfg
        ⟨50,regs b c.left c.right c.state description 0 0 clock⟩)
      (evalCost description c clock) =
      Source284GraphCandidateMirror.mapCfg ⟨50,regs b
        (Source284Relative.run description c clock).left
        (Source284Relative.run description c clock).right
        (Source284Relative.run description c clock).state description 0 0 0⟩ ∧
    target.system.wordFrom
      (Source284GraphCandidateMirror.mapCfg
        ⟨50,regs b c.left c.right c.state description 0 0 clock⟩)
      (evalCost description c clock) = [] := by
  exact Source284GraphCandidateMirror.conditional_candidate_evaluate b description clock c
    (evaluate b description c clock).2

end Shared.Beeping.NPcoNP.Source284GraphBlockEvaluator
