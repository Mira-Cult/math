import Shared.Beeping.NPcoNP.Source284GraphCandidateBound

/-! Compose the source reference, candidate clock and candidate witness-bound
setup in the pinned register graph. Physical-machine refinement remains open. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphCandidateReady
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphCandidateBoundRows
open Shared.Beeping.NPcoNP.Source284GraphCandidateBound
open Shared.Beeping.NPcoNP.Source284GraphCandidateHandoff
abbrev Bank := PASoundness.RegisterMachine.Bank 12

theorem bank_original (b : Bank) (h10 : b 10=0) (h11 : b 11=0) :
    bank b (b 6) (b 7) 0 0 = b := by
  funext i
  fin_cases i <;> simp [bank,h10,h11]

def boundBank (b : Bank) : Bank := bank b (b 6) (2^(b 6)) 0 0

/-- The candidate-bound loop runs from the actual post-clock bank. -/
theorem bound_from_pc104 (b : Bank) (h10 : b 10=0) (h11 : b 11=0) :
    0 < boundCost (b 6) (b 7) ∧
      target.system.advance ⟨104,b⟩ (boundCost (b 6) (b 7)) = ⟨115,boundBank b⟩ ∧
      target.system.wordFrom ⟨104,b⟩ (boundCost (b 6) (b 7)) = [] := by
  have h := bound b (b 6) (b 7)
  simpa [Source284GraphApplyLoops.Seg,bank_original b h10 h11,boundBank] using h

/-- The complete reference and candidate setup reaches the candidate-search
entry, with the exact original input, source reference bit, candidate index,
source clock and exhaustive witness bound. All steps are finite and silent. -/
theorem candidate_ready_from_pc2 (b : Bank) (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    ∃ (time : Nat) (out : Bank), 0 < time ∧
      target.system.advance ⟨2,b⟩ time = ⟨115,out⟩ ∧
      target.system.wordFrom ⟨2,b⟩ time = [] ∧
      out 4 = b 4 ∧ out 3 = b 3 ∧ out 5 = Source284Parser.length (b 4) ∧
      out 6 = Source284Comparison.clock (b 3) (b 4) ∧
      out 7 = 2^(Source284Comparison.clock (b 3) (b 4)) ∧
      out 0 = (if Source284Comparison.reference (b 4) then 1 else 0) ∧
      out 9 = 0 ∧ out 10 = 0 ∧ out 11 = 0 := by
  obtain ⟨k,r,hk,ha,hw,hi,hj,hn,hc,hbit,hs9,hs10,hs11⟩ :=
    reference_and_clock b h9 h10 h11
  have hb := bound_from_pc104 r hs10 hs11
  refine ⟨k+boundCost (r 6) (r 7),boundBank r,by omega,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [WordEventSystem.advance_add,ha,hb.2.1]
  · rw [WordEventSystem.wordFrom_add,ha,hw,hb.2.2]; rfl
  · simpa [boundBank,bank] using hi
  · simpa [boundBank,bank] using hj
  · simpa [boundBank,bank] using hn
  · simpa [boundBank,bank] using hc
  · simp [boundBank,bank,hc]
  · simpa [boundBank,bank] using hbit
  · simpa [boundBank,bank] using hs9
  · simp [boundBank,bank]
  · simp [boundBank,bank]

/-- The parsed embedded producer graph realizes the same full setup trace. -/
theorem embedded_candidate_ready (b : Bank) (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    ∃ (time : Nat) (out : Bank), 0 < time ∧
      ((Grammar284ParseSource.parse Grammar284.SourceChars.source.toList).bind
        (fun g => Grammar284.coreGraph g 53)).bind
        (fun g => GraphExtendedTrace.graphTrace g ⟨2,b⟩ time) = some (⟨115,out⟩,[]) ∧
      out 4 = b 4 ∧ out 3 = b 3 ∧ out 5 = Source284Parser.length (b 4) ∧
      out 6 = Source284Comparison.clock (b 3) (b 4) ∧
      out 7 = 2^(Source284Comparison.clock (b 3) (b 4)) ∧
      out 0 = (if Source284Comparison.reference (b 4) then 1 else 0) ∧
      out 9 = 0 ∧ out 10 = 0 ∧ out 11 = 0 := by
  obtain ⟨time,out,ht,ha,hw,hi,hj,hn,hc,hbound,hbit,hs9,hs10,hs11⟩ :=
    candidate_ready_from_pc2 b h9 h10 h11
  refine ⟨time,out,ht,?_,hi,hj,hn,hc,hbound,hbit,hs9,hs10,hs11⟩
  rw [Grammar284CoreTrace.embeddedGraph_run,ha,hw]

end Shared.Beeping.NPcoNP.Source284GraphCandidateReady
