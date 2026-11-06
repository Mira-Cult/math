import Shared.Beeping.NPcoNP.Source284GraphBlockEvaluator
import Shared.Beeping.NPcoNP.Source284GraphAttemptComplete

/-! Unconditional candidate-block bounded evaluator, obtained from the
checked reference evaluator and the proved block-residence invariant. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphCandidateEvaluator
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyRow (regs)
open Shared.Beeping.NPcoNP.Source284GraphCandidateMirror
open Shared.Beeping.NPcoNP.Source284GraphBlockEvaluator
open Shared.Beeping.NPcoNP.Source284GraphEvaluator (evalCost)
open Shared.Beeping.NPcoNP.Source284Relative
abbrev Bank := PASoundness.RegisterMachine.Bank 12

/-- Once the mirrored evaluator has exhausted its clock, its next graph
transition reaches the candidate result dispatch at PC 176. -/
theorem zero_clock_exit (b : Bank) (l r s d : Nat) :
    target.system.step (mapCfg ⟨50,regs b l r s d 0 0 0⟩) =
      (⟨176,swapBank (regs b l r s d 0 0 0)⟩,[]) := by
  have h := block_step ⟨0,by decide⟩ (regs b l r s d 0 0 0)
  have hs := Source284GraphAttemptComplete.row50_zero b l r s d 0 0
  simpa [mapCfg,shiftState,hs] using h

/-- Every finite candidate evaluator clock completes in a finite silent
graph segment and reaches its real result dispatch. No block-residence
hypothesis remains. -/
theorem evaluate_to_dispatch (b : Bank) (description clock : Nat) (c : Source284Relative.Config) :
    0 < evalCost description c clock+1 ∧
    target.system.advance
      (mapCfg ⟨50,regs b c.left c.right c.state description 0 0 clock⟩)
      (evalCost description c clock+1) =
      ⟨176,swapBank (regs b (Source284Relative.run description c clock).left
        (Source284Relative.run description c clock).right
        (Source284Relative.run description c clock).state description 0 0 0)⟩ ∧
    target.system.wordFrom
      (mapCfg ⟨50,regs b c.left c.right c.state description 0 0 clock⟩)
      (evalCost description c clock+1) = [] := by
  let out := Source284Relative.run description c clock
  have he := candidate_evaluate b description clock c
  have hx := zero_clock_exit b out.left out.right out.state description
  refine ⟨by omega,?_,?_⟩
  · rw [WordEventSystem.advance_add,he.1]
    simpa [out,WordEventSystem.advance,hx]
  · rw [WordEventSystem.wordFrom_add,he.1,he.2]
    simpa [out,WordEventSystem.wordFrom,WordEventSystem.advance,hx]

/-- The same candidate evaluator segment is a trace of the graph parsed
from the embedded producer grammar. -/
theorem embedded_evaluate_to_dispatch (b : Bank) (description clock : Nat) (c : Source284Relative.Config) :
    ((Grammar284ParseSource.parse Grammar284.SourceChars.source.toList).bind
      (fun g => Grammar284.coreGraph g 53)).bind
      (fun g => GraphExtendedTrace.graphTrace g
        (mapCfg ⟨50,regs b c.left c.right c.state description 0 0 clock⟩)
        (evalCost description c clock+1)) =
    some (⟨176,swapBank (regs b (Source284Relative.run description c clock).left
      (Source284Relative.run description c clock).right
      (Source284Relative.run description c clock).state description 0 0 0)⟩,[]) := by
  rw [Grammar284CoreTrace.embeddedGraph_run]
  have h := evaluate_to_dispatch b description clock c
  rw [h.2.1,h.2.2]

end Shared.Beeping.NPcoNP.Source284GraphCandidateEvaluator
