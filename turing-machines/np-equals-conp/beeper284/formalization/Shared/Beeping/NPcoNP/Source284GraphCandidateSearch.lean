import Shared.Beeping.NPcoNP.Source284GraphCandidateBounded

/-! Complete finite descending candidate-certificate search in the pinned
register graph, with every attempt charged and no event output. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphCandidateSearch
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyLoops (Seg cat)
open Shared.Beeping.NPcoNP.Source284GraphApplyRow (regs)
open Shared.Beeping.NPcoNP.Source284GraphCandidateMirror
open Shared.Beeping.NPcoNP.Source284GraphCandidateSetup
open Shared.Beeping.NPcoNP.Source284GraphCandidateBounded
open Shared.Beeping.NPcoNP.Source284Relative
abbrev Bank := PASoundness.RegisterMachine.Bank 12

@[simp] theorem final3 (b : Bank) : finalBank b 3 = b 3 := by simp [finalBank,regs,swapBank,swapIndex,ready,write]
@[simp] theorem final4 (b : Bank) : finalBank b 4 = b 4 := by simp [finalBank,regs,swapBank,swapIndex,ready,write]
@[simp] theorem final6 (b : Bank) : finalBank b 6 = b 6 := by simp [finalBank,regs,swapBank,swapIndex,ready,write]
@[simp] theorem final7 (b : Bank) : finalBank b 7 = b 7-1 := by simp [finalBank,regs,swapBank,swapIndex,ready,write]
@[simp] theorem final9 (b : Bank) : finalBank b 9 = 0 := by simp [finalBank,regs,swapBank,swapIndex]
@[simp] theorem final10 (b : Bank) : finalBank b 10 = 0 := by simp [finalBank,regs,swapBank,swapIndex]
@[simp] theorem final11 (b : Bank) : finalBank b 11 = 0 := by simp [finalBank,regs,swapBank,swapIndex]

theorem row115_zero (b : Bank) (h : b 7=0) :
    target.system.step ⟨115,b⟩ = (⟨181,b⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,h]

theorem acceptBound_succ (description input clock n : Nat) :
    acceptBound description input clock (n+1) =
      (accepts description input n clock || acceptBound description input clock n) := by
  simp [acceptBound,List.range_succ,Bool.or_comm]

def searchCost (b : Bank) : Nat → Nat
  | 0 => 1
  | n+1 => attemptCost b +
      if accepts (b 3) (b 4) (b 7-1) (b 6) then 0 else searchCost (finalBank b) n

def searchBank (b : Bank) : Nat → Bank
  | 0 => b
  | n+1 => if accepts (b 3) (b 4) (b 7-1) (b 6) then finalBank b else searchBank (finalBank b) n

/-- Every finite candidate-certificate search finishes silently: it reaches
PC 178 exactly when at least one certificate below the bound accepts, and
otherwise reaches PC 181. Scratch registers must be clear at entry. -/
theorem search (b : Bank) (n : Nat) (h7 : b 7=n)
    (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    0 < searchCost b n ∧
    Seg ⟨115,b⟩
      ⟨if acceptBound (b 3) (b 4) (b 6) n then 178 else 181, searchBank b n⟩
      (searchCost b n) := by
  induction n generalizing b with
  | zero =>
    have hs := row115_zero b (by omega)
    refine ⟨by simp [searchCost],?_⟩
    simpa [searchCost,searchBank,acceptBound,Seg,WordEventSystem.advance,
      WordEventSystem.wordFrom,hs]
  | succ n ih =>
    have hp : 0 < b 7 := by omega
    have hnum : b 7-1 = n := by omega
    have ha := Source284GraphCandidateBounded.attempt b hp h9 h10 h11
    have hnext : finalBank b 7 = n := by rw [final7,hnum]
    by_cases hac : accepts (b 3) (b 4) n (b 6) = true
    · have he : accepts (b 3) (b 4) (b 7-1) (b 6) = true := by simpa [hnum] using hac
      have hb : acceptBound (b 3) (b 4) (b 6) (n+1) = true := by simp [acceptBound_succ,hac]
      refine ⟨?_,?_⟩
      · simp only [searchCost,he,if_true,add_zero]
        exact ha.1
      · simpa [searchCost,searchBank,he,hb] using ha.2
    · have hn : accepts (b 3) (b 4) n (b 6) = false := by cases h : accepts (b 3) (b 4) n (b 6) <;> simp_all
      have he : accepts (b 3) (b 4) (b 7-1) (b 6) = false := by simpa [hnum] using hn
      have hi := ih (finalBank b) hnext (final9 b) (final10 b) (final11 b)
      have hbound : acceptBound (b 3) (b 4) (b 6) (n+1) = acceptBound (b 3) (b 4) (b 6) n := by
        simp [acceptBound_succ,hn]
      have hfirst : Seg ⟨115,b⟩ ⟨115,finalBank b⟩ (attemptCost b) := by
        simpa [he] using ha.2
      have hseg := cat hfirst hi.2
      refine ⟨?_,?_⟩
      · simp only [searchCost,he,Bool.false_eq_true,if_false]
        omega
      · simpa [searchCost,searchBank,he,hbound,final3,final4,final6] using hseg

/-- The same finite search is executed by the graph parsed from the embedded
producer grammar. This is not yet a physical tape-machine theorem. -/
theorem embedded_search (b : Bank) (n : Nat) (h7 : b 7=n)
    (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    ((Grammar284ParseSource.parse Grammar284.SourceChars.source.toList).bind
      (fun g => Grammar284.coreGraph g 53)).bind
      (fun g => GraphExtendedTrace.graphTrace g ⟨115,b⟩ (searchCost b n)) =
    some (⟨if acceptBound (b 3) (b 4) (b 6) n then 178 else 181,searchBank b n⟩,[]) := by
  rw [Grammar284CoreTrace.embeddedGraph_run]
  have h := (search b n h7 h9 h10 h11).2
  rw [h.1,h.2]

end Shared.Beeping.NPcoNP.Source284GraphCandidateSearch
