import Shared.Beeping.NPcoNP.Source284GraphCandidateSearch

/-! Full reference and candidate witness searches on the parsed register graph.
The final comparison and physical blank-tape refinement are separate obligations. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphBothPhases
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyRow (regs)
open Shared.Beeping.NPcoNP.Source284GraphCandidateMirror
open Shared.Beeping.NPcoNP.Source284GraphCandidateSetup
open Shared.Beeping.NPcoNP.Source284GraphCandidateBounded
open Shared.Beeping.NPcoNP.Source284GraphCandidateSearch
abbrev Bank := PASoundness.RegisterMachine.Bank 12

@[simp] theorem final0 (b : Bank) : finalBank b 0 = b 0 := by
  simp [finalBank,regs,swapBank,swapIndex,ready,write]

theorem searchBank_zero (b : Bank) (n : Nat) : searchBank b n 0 = b 0 := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [searchBank]
    split
    · exact final0 b
    · rw [ih,final0]

theorem searchBank_three (b : Bank) (n : Nat) : searchBank b n 3 = b 3 := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [searchBank]
    split
    · exact final3 b
    · rw [ih,final3]

theorem searchBank_input (b : Bank) (n : Nat) : searchBank b n 4 = b 4 := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    simp only [searchBank]
    split
    · exact final4 b
    · rw [ih,final4]

theorem searchBank_scratch (b : Bank) (n : Nat)
    (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    searchBank b n 9=0 ∧ searchBank b n 10=0 ∧ searchBank b n 11=0 := by
  induction n generalizing b with
  | zero => exact ⟨h9,h10,h11⟩
  | succ n ih =>
    simp only [searchBank]
    split
    · exact ⟨final9 b,final10 b,final11 b⟩
    · exact ih (finalBank b) (final9 b) (final10 b) (final11 b)

/-- From a supplied PC-2 bank with clear scratch registers, both bounded
searches complete in a positive finite silent segment. The candidate branch
and retained reference bit are the exact executable source Booleans. -/
theorem both_from_pc2 (b : Bank) (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    ∃ (time : Nat) (out : Bank), 0 < time ∧
      target.system.advance ⟨2,b⟩ time =
        ⟨if Source284Comparison.candidate (b 3) (b 4) then 178 else 181,out⟩ ∧
      target.system.wordFrom ⟨2,b⟩ time = [] ∧
      out 0 = (if Source284Comparison.reference (b 4) then 1 else 0) ∧
      out 3 = b 3 ∧ out 4 = b 4 ∧ out 9=0 ∧ out 10=0 ∧ out 11=0 := by
  obtain ⟨k,r,hk,ha,hw,hi,hj,hn,hc,hbound,hbit,hs9,hs10,hs11⟩ :=
    Source284GraphCandidateReady.candidate_ready_from_pc2 b h9 h10 h11
  let n := 2^(Source284Comparison.clock (b 3) (b 4))
  have hs := search r n (by simpa [n] using hbound) hs9 hs10 hs11
  let out := searchBank r n
  have hcand : Source284Relative.acceptBound (r 3) (r 4) (r 6) n =
      Source284Comparison.candidate (b 3) (b 4) := by
    simp [Source284Comparison.candidate,hj,hi,hc,n]
  have hout0 : out 0 = (if Source284Comparison.reference (b 4) then 1 else 0) := by
    simpa [out,hbit] using searchBank_zero r n
  have hout3 : out 3=b 3 := by simpa [out,hj] using searchBank_three r n
  have hout4 : out 4=b 4 := by simpa [out,hi] using searchBank_input r n
  have hscratch : out 9=0 ∧ out 10=0 ∧ out 11=0 :=
    searchBank_scratch r n hs9 hs10 hs11
  refine ⟨k+searchCost r n,out,by omega,?_,?_,hout0,hout3,hout4,hscratch.1,hscratch.2.1,hscratch.2.2⟩
  · rw [WordEventSystem.advance_add,ha,hs.2.1,hcand]
  · rw [WordEventSystem.wordFrom_add,ha,hw,hs.2.2]; rfl

/-- The same two-phase segment occurs in the graph parsed from the pinned
embedded producer grammar. -/
theorem embedded_both_from_pc2 (b : Bank) (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    ∃ (time : Nat) (out : Bank), 0 < time ∧
      ((Grammar284ParseSource.parse Grammar284.SourceChars.source.toList).bind
        (fun g => Grammar284.coreGraph g 53)).bind
        (fun g => GraphExtendedTrace.graphTrace g ⟨2,b⟩ time) =
          some (⟨if Source284Comparison.candidate (b 3) (b 4) then 178 else 181,out⟩,[]) ∧
      out 0 = (if Source284Comparison.reference (b 4) then 1 else 0) ∧
      out 3 = b 3 ∧ out 4 = b 4 ∧ out 9=0 ∧ out 10=0 ∧ out 11=0 := by
  obtain ⟨time,out,ht,ha,hw,h0,h3,h4,h9',h10',h11'⟩ := both_from_pc2 b h9 h10 h11
  refine ⟨time,out,ht,?_,h0,h3,h4,h9',h10',h11'⟩
  rw [Grammar284CoreTrace.embeddedGraph_run,ha,hw]

end Shared.Beeping.NPcoNP.Source284GraphBothPhases
