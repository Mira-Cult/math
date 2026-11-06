import Shared.Beeping.NPcoNP.Source284GraphReferenceBounded

/-! The checked register graph's complete descending reference-certificate
search. Each attempt and the exhaustion branch are paid silent segments. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphReferenceSearch
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyRow
open Shared.Beeping.NPcoNP.Source284GraphApplyLoops
open Shared.Beeping.NPcoNP.Source284GraphReferenceAttempt
open Shared.Beeping.NPcoNP.Source284GraphReferenceBounded
open Shared.Beeping.NPcoNP.Source284Relative
abbrev Bank := PASoundness.RegisterMachine.Bank 12

@[simp] theorem final5 (b : Bank) : finalBank b 5 = b 5 := by simp [finalBank,regs,ready,write]
@[simp] theorem final6 (b : Bank) : finalBank b 6 = b 6 := by simp [finalBank,regs,ready,write]
@[simp] theorem final7 (b : Bank) : finalBank b 7 = b 7-1 := by simp [finalBank,regs,ready,write]
@[simp] theorem final9 (b : Bank) : finalBank b 9 = 0 := by simp [finalBank,regs]
@[simp] theorem final10 (b : Bank) : finalBank b 10 = 0 := by simp [finalBank,regs]
@[simp] theorem final11 (b : Bank) : finalBank b 11 = 0 := by simp [finalBank,regs]

theorem row31_zero (b : Bank) (h : b 7=0) :
    target.system.step ⟨31,b⟩ = (⟨89,b⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,h]

theorem acceptBound_succ (description clock n : Nat) :
    acceptBound description 0 clock (n+1) =
      (accepts description 0 n clock || acceptBound description 0 clock n) := by
  simp [acceptBound,List.range_succ,Bool.or_comm]

/-- Finite graph cost along the actual descending attempt trajectory.
The bounded acceptance test is an executable total predicate. -/
def searchCost (b : Bank) : Nat → Nat
  | 0 => 1
  | n+1 => referenceCost b +
      if accepts (b 6) 0 (b 7-1) (b 5) then 0 else searchCost (finalBank b) n

/-- The full final bank reached at the accepting or exhausted branch. -/
def searchBank (b : Bank) : Nat → Bank
  | 0 => b
  | n+1 => if accepts (b 6) 0 (b 7-1) (b 5) then finalBank b else searchBank (finalBank b) n

/-- Every finite reference search terminates, without beeps, at PC 87 if
some bounded certificate accepts and at PC 89 otherwise. The theorem is
uniform over all descriptions, clocks, and supplied banks with zero scratch. -/
theorem search (b : Bank) (n : Nat) (h7 : b 7=n)
    (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    0 < searchCost b n ∧
    Seg ⟨31,b⟩
      ⟨if acceptBound (b 6) 0 (b 5) n then 87 else 89, searchBank b n⟩
      (searchCost b n) := by
  induction n generalizing b with
  | zero =>
    have hs := row31_zero b (by omega)
    refine ⟨by simp [searchCost],?_⟩
    simpa [searchCost,searchBank,acceptBound,Seg,WordEventSystem.advance,
      WordEventSystem.wordFrom,hs]
  | succ n ih =>
    have hp : 0 < b 7 := by omega
    have hnum : b 7-1 = n := by omega
    have ha := Source284GraphReferenceBounded.reference_attempt b hp h9 h10 h11
    have hnext : finalBank b 7 = n := by rw [final7,hnum]
    by_cases hac : accepts (b 6) 0 n (b 5) = true
    · have he : accepts (b 6) 0 (b 7-1) (b 5) = true := by simpa [hnum] using hac
      have hb : acceptBound (b 6) 0 (b 5) (n+1) = true := by simp [acceptBound_succ,hac]
      refine ⟨?_,?_⟩
      · simp only [searchCost,he,if_true,add_zero]
        exact ha.1
      · simpa [searchCost,searchBank,he,hb] using ha.2
    · have hn : accepts (b 6) 0 n (b 5) = false := by cases h : accepts (b 6) 0 n (b 5) <;> simp_all
      have he : accepts (b 6) 0 (b 7-1) (b 5) = false := by simpa [hnum] using hn
      have hi := ih (finalBank b) hnext (final9 b) (final10 b) (final11 b)
      have hbound : acceptBound (b 6) 0 (b 5) (n+1) = acceptBound (b 6) 0 (b 5) n := by
        simp [acceptBound_succ,hn]
      have hfirst : Seg ⟨31,b⟩ ⟨31,finalBank b⟩ (referenceCost b) := by
        simpa [he] using ha.2
      have hseg := cat hfirst hi.2
      refine ⟨?_,?_⟩
      · simp only [searchCost,he,Bool.false_eq_true,if_false]
        omega
      · simpa [searchCost,searchBank,he,hbound,final5,final6] using hseg

/-- The complete finite reference search is a trace of the graph extracted
from the pinned embedded grammar. -/
theorem embedded_search (b : Bank) (n : Nat) (h7 : b 7=n)
    (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    ((Grammar284ParseSource.parse Grammar284.SourceChars.source.toList).bind
      (fun g => Grammar284.coreGraph g 53)).bind
      (fun g => GraphExtendedTrace.graphTrace g ⟨31,b⟩ (searchCost b n)) =
    some (⟨if acceptBound (b 6) 0 (b 5) n then 87 else 89,searchBank b n⟩,[]) := by
  rw [Grammar284CoreTrace.embeddedGraph_run]
  have h := (search b n h7 h9 h10 h11).2
  rw [h.1,h.2]

end Shared.Beeping.NPcoNP.Source284GraphReferenceSearch
