import Shared.Beeping.NPcoNP.Source284GraphAttemptComplete

/-! One complete descending reference-certificate attempt, from the actual
checked graph's PC 31 through the bounded evaluator's branch. This does not
yet prove the outer search loop or the physical tape implementation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphReferenceBounded
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyRow
open Shared.Beeping.NPcoNP.Source284GraphApplyLoops
open Shared.Beeping.NPcoNP.Source284GraphReferenceAttempt
open Shared.Beeping.NPcoNP.Source284GraphAttemptComplete
open Shared.Beeping.NPcoNP.Source284Relative
abbrev Bank := PASoundness.RegisterMachine.Bank 12

def setupCost (b : Bank) : Nat := (7*(b 7-1)+b 8+5) + (b 1+b 2+7*b 5+6)

def referenceCost (b : Bank) : Nat :=
  setupCost b + attemptCost (b 6) 0 (b 7-1) (b 5)

def finalSource (b : Bank) : Source284Relative.Config :=
  Source284Relative.run (b 6) (Source284Relative.initial 0 (b 7-1)) (b 5)

def finalBank (b : Bank) : Bank :=
  let out := finalSource b
  regs (ready b) out.left out.right out.state (b 6) 0 0 0

/-- The supplied scratch conditions make the actual attempt initializer
exactly the evaluator's standard source input configuration. -/
theorem ready_regs (b : Bank) (h9 : b 9=0) (h10 : b 10=0) :
    regs (ready b) (b 7-1) 0 1 (b 6) 0 0 (b 5) = ready b := by
  funext i
  fin_cases i <;> simp [regs,ready,write,h9,h10]

/-- A positive counter picks certificate `b7-1`, simulates it to the source
clock, and reaches PC 87 on acceptance or PC 31 on rejection. All emitted
words are empty and every step is paid. -/
theorem reference_attempt (b : Bank) (h7 : 0 < b 7)
    (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    0 < referenceCost b ∧
    Seg ⟨31,b⟩
      ⟨if accepts (b 6) 0 (b 7-1) (b 5) then 87 else 31,finalBank b⟩
      (referenceCost b) := by
  have hs := Source284GraphReferenceAttempt.reference_attempt b h7 h9 h10 h11
  have ha := attempt (ready b) (b 6) 0 (b 7-1) (b 5)
  have hsetup : Seg ⟨31,b⟩ ⟨50,ready b⟩ (setupCost b) := by
    simpa only [Seg,setupCost] using hs.2
  have hexec : Seg ⟨50,ready b⟩
      ⟨if accepts (b 6) 0 (b 7-1) (b 5) then 87 else 31,finalBank b⟩
      (attemptCost (b 6) 0 (b 7-1) (b 5)) := by
    simpa only [ready_regs b h9 h10,finalBank,finalSource] using ha.2
  refine ⟨?_,?_⟩
  · unfold referenceCost
    have hp := ha.1
    omega
  · exact cat hsetup hexec

/-- The same complete certificate attempt is a trace of the parsed pinned
producer graph. -/
theorem embedded_reference_attempt (b : Bank) (h7 : 0 < b 7)
    (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    ((Grammar284ParseSource.parse Grammar284.SourceChars.source.toList).bind
      (fun g => Grammar284.coreGraph g 53)).bind
      (fun g => GraphExtendedTrace.graphTrace g ⟨31,b⟩ (referenceCost b)) =
    some (⟨if accepts (b 6) 0 (b 7-1) (b 5) then 87 else 31,finalBank b⟩,[]) := by
  rw [Grammar284CoreTrace.embeddedGraph_run]
  have h := (reference_attempt b h7 h9 h10 h11).2
  rw [h.1,h.2]

end Shared.Beeping.NPcoNP.Source284GraphReferenceBounded
