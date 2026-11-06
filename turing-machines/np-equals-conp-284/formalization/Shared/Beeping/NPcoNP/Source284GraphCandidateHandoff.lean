import Shared.Beeping.NPcoNP.Source284GraphCandidateClock

/-! Compose the complete reference phase with the candidate clock on the
checked graph. This is a supplied-bank result, not a physical tape binding. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphCandidateHandoff
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphCandidateClockRows
open Shared.Beeping.NPcoNP.Source284GraphCandidateClock
open Shared.Beeping.NPcoNP.Source284GraphReferenceComplete
abbrev Bank := PASoundness.RegisterMachine.Bank 12

theorem bank_original (b : Bank) (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    bank b (b 3) (b 5) (b 6) 0 0 0 = b := by
  funext i
  fin_cases i <;> simp [bank,h9,h10,h11]

def clockBank (b : Bank) : Bank := bank b (b 3) (b 5) ((b 5+1)^(b 3)) 0 0 0

/-- The candidate clock starts from the actual post-reference bank. -/
theorem clock_from_pc89 (b : Bank) (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    0 < clockCost (b 3) (b 5) (b 6) ∧
      target.system.advance ⟨89,b⟩ (clockCost (b 3) (b 5) (b 6)) = ⟨104,clockBank b⟩ ∧
      target.system.wordFrom ⟨89,b⟩ (clockCost (b 3) (b 5) (b 6)) = [] := by
  have h := clock b (b 3) (b 5) (b 6)
  simpa [Source284GraphApplyLoops.Seg,bank_original b h9 h10 h11,clockBank] using h

/-- Starting at the reference input handoff, the graph performs the complete
reference search and then computes the exact source candidate clock. -/
theorem reference_and_clock (b : Bank) (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    ∃ (time : Nat) (out : Bank), 0 < time ∧
      target.system.advance ⟨2,b⟩ time = ⟨104,out⟩ ∧
      target.system.wordFrom ⟨2,b⟩ time = [] ∧
      out 4 = b 4 ∧ out 3 = b 3 ∧ out 5 = Source284Parser.length (b 4) ∧
      out 6 = Source284Comparison.clock (b 3) (b 4) ∧
      out 0 = (if Source284Comparison.reference (b 4) then 1 else 0) ∧
      out 9 = 0 ∧ out 10 = 0 ∧ out 11 = 0 := by
  obtain ⟨k,r,hk,ha,hw,hinv,hbit⟩ := reference_ready_from_pc2 b h9 h10 h11
  obtain ⟨hi,hj,hn,hs9,hs10,hs11⟩ := hinv
  have hc := clock_from_pc89 r hs9 hs10 hs11
  refine ⟨k+clockCost (r 3) (r 5) (r 6),clockBank r,by omega,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [WordEventSystem.advance_add,ha,hc.2.1]
  · rw [WordEventSystem.wordFrom_add,ha,hw,hc.2.2]; rfl
  · simpa [clockBank,bank] using hi
  · simpa [clockBank,bank] using hj
  · simpa [clockBank,bank] using hn
  · simp [clockBank,bank,Source284Comparison.clock,hj,hn,hi]
  · simpa [clockBank,bank] using hbit
  · simp [clockBank,bank]
  · simp [clockBank,bank]
  · simp [clockBank,bank]

/-- The parsed embedded producer graph realizes the same finite silent
reference-and-clock segment. -/
theorem embedded_reference_and_clock (b : Bank) (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    ∃ (time : Nat) (out : Bank), 0 < time ∧
      ((Grammar284ParseSource.parse Grammar284.SourceChars.source.toList).bind
        (fun g => Grammar284.coreGraph g 53)).bind
        (fun g => GraphExtendedTrace.graphTrace g ⟨2,b⟩ time) = some (⟨104,out⟩,[]) ∧
      out 4 = b 4 ∧ out 3 = b 3 ∧ out 5 = Source284Parser.length (b 4) ∧
      out 6 = Source284Comparison.clock (b 3) (b 4) ∧
      out 0 = (if Source284Comparison.reference (b 4) then 1 else 0) ∧
      out 9 = 0 ∧ out 10 = 0 ∧ out 11 = 0 := by
  obtain ⟨time,out,ht,ha,hw,hi,hj,hn,hc,hbit,hs9,hs10,hs11⟩ :=
    reference_and_clock b h9 h10 h11
  refine ⟨time,out,ht,?_,hi,hj,hn,hc,hbit,hs9,hs10,hs11⟩
  rw [Grammar284CoreTrace.embeddedGraph_run,ha,hw]

end Shared.Beeping.NPcoNP.Source284GraphCandidateHandoff
