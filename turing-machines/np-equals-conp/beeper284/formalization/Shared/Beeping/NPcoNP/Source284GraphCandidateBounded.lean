import Shared.Beeping.NPcoNP.Source284GraphCandidateSetup

/-! One complete candidate witness attempt from the actual graph search entry. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphCandidateBounded
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyLoops (Seg cat)
open Shared.Beeping.NPcoNP.Source284GraphApplyRow (regs)
open Shared.Beeping.NPcoNP.Source284GraphCandidateMirror
open Shared.Beeping.NPcoNP.Source284GraphCandidateSetup
open Shared.Beeping.NPcoNP.Source284Relative
abbrev Bank := PASoundness.RegisterMachine.Bank 12

def attemptCost (b : Bank) : Nat := setupCost b +
  Source284GraphCandidateAttempt.attemptCost (b 3) (b 4) (b 7-1) (b 6)

def finalSource (b : Bank) : Source284Relative.Config :=
  Source284Relative.run (b 3) (Source284Relative.initial (b 4) (b 7-1)) (b 6)

def finalBank (b : Bank) : Bank :=
  let out := finalSource b
  swapBank (regs (swapBank (ready b)) out.left out.right out.state (b 3) 0 0 0)

/-- The setup bank is exactly the evaluator's standard source configuration. -/
theorem ready_cfg (b : Bank) (h9 : b 9=0) (h10 : b 10=0) :
    mapCfg ⟨50,regs (swapBank (ready b)) (b 7-1) (b 4) 1 (b 3) 0 0 (b 6)⟩ =
      ⟨141,ready b⟩ := by
  change (⟨141,swapBank (regs (swapBank (ready b)) (b 7-1) (b 4) 1 (b 3) 0 0 (b 6))⟩ : Cfg) = ⟨141,ready b⟩
  congr 1
  funext i
  fin_cases i <;> simp [mapCfg,shiftState,swapBank,swapIndex,regs,ready,write,h9,h10]

/-- Each positive counter chooses the next certificate and executes its entire
clocked source computation. Both outcomes take finite silent graph segments. -/
theorem attempt (b : Bank) (h7 : 0 < b 7)
    (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    0 < attemptCost b ∧
    Seg ⟨115,b⟩
      ⟨if accepts (b 3) (b 4) (b 7-1) (b 6) then 178 else 115, finalBank b⟩
      (attemptCost b) := by
  have hs := setup b h7 h9 h10 h11
  have he := Source284GraphCandidateAttempt.attempt (swapBank (ready b)) (b 3) (b 4) (b 7-1) (b 6)
  have hexec : Seg ⟨141,ready b⟩
      ⟨if accepts (b 3) (b 4) (b 7-1) (b 6) then 178 else 115,finalBank b⟩
      (Source284GraphCandidateAttempt.attemptCost (b 3) (b 4) (b 7-1) (b 6)) := by
    simpa only [ready_cfg b h9 h10,finalBank,finalSource] using he.2
  refine ⟨?_,?_⟩
  · unfold attemptCost; have hp := he.1; omega
  · exact cat hs.2 hexec

end Shared.Beeping.NPcoNP.Source284GraphCandidateBounded
