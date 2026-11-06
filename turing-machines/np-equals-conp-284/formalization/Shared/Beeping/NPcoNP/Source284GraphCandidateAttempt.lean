import Shared.Beeping.NPcoNP.Source284GraphCandidateEvaluator

/-! Complete the candidate evaluator's silent accept/reject dispatch. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphCandidateAttempt
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyRow (regs)
open Shared.Beeping.NPcoNP.Source284GraphCandidateMirror
open Shared.Beeping.NPcoNP.Source284GraphCandidateEvaluator
open Shared.Beeping.NPcoNP.Source284GraphApplyLoops (Seg cat)
open Shared.Beeping.NPcoNP.Source284GraphEvaluator (evalCost)
open Shared.Beeping.NPcoNP.Source284Relative
abbrev Bank := PASoundness.RegisterMachine.Bank 12

theorem row176_zero (b : Bank) (l r d : Nat) :
    target.system.step ⟨176,swapBank (regs b l r 0 d 0 0 0)⟩ =
      (⟨178,swapBank (regs b l r 0 d 0 0 0)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,swapBank,swapIndex,regs]

theorem row176_positive (b : Bank) (l r s d : Nat) :
    target.system.step ⟨176,swapBank (regs b l r (s+1) d 0 0 0)⟩ =
      (⟨177,swapBank (regs b l r s d 0 0 0)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,swapBank,swapIndex,regs]
  funext i
  fin_cases i <;> simp [write,swapBank,swapIndex,regs]

theorem row177 (b : Bank) (l r s d : Nat) :
    target.system.step ⟨177,swapBank (regs b l r s d 0 0 0)⟩ =
      (⟨115,swapBank (regs b l r (s+1) d 0 0 0)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,swapBank,swapIndex,regs]
  funext i
  fin_cases i <;> simp [write,swapBank,swapIndex,regs]

def exitCost (s : Nat) : Nat := if s=0 then 1 else 2
def exitPc (s : Nat) : Fin 185 := if s=0 then 178 else 115

theorem exit (b : Bank) (l r s d : Nat) :
    Seg ⟨176,swapBank (regs b l r s d 0 0 0)⟩
      ⟨exitPc s,swapBank (regs b l r s d 0 0 0)⟩ (exitCost s) := by
  cases s with
  | zero => simp [exitPc,exitCost,Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row176_zero]
  | succ s => simp [exitPc,exitCost,Seg,WordEventSystem.advance,WordEventSystem.wordFrom,
      row176_positive,row177]

def attemptCost (description input certificate clock : Nat) : Nat :=
  let c := Source284Relative.initial input certificate
  evalCost description c clock + 1 + exitCost (Source284Relative.run description c clock).state

/-- A finite clocked candidate computation reaches the correct branch silently,
with the entire numeric source output retained. -/
theorem attempt (b : Bank) (description input certificate clock : Nat) :
    let c := Source284Relative.initial input certificate
    let out := Source284Relative.run description c clock
    0 < attemptCost description input certificate clock ∧
    Seg (mapCfg ⟨50,regs b certificate input 1 description 0 0 clock⟩)
      ⟨if accepts description input certificate clock then 178 else 115,
        swapBank (regs b out.left out.right out.state description 0 0 0)⟩
      (attemptCost description input certificate clock) := by
  let c := Source284Relative.initial input certificate
  let out := Source284Relative.run description c clock
  have he := evaluate_to_dispatch b description clock c
  have hx := exit b out.left out.right out.state description
  have hall := cat ⟨he.2.1,he.2.2⟩ hx
  have hp : 0 < exitCost out.state := by unfold exitCost; split <;> decide
  have hp' : 0 < exitCost (Source284Relative.run description
      (Source284Relative.initial input certificate) clock).state := by simpa [out,c] using hp
  refine ⟨by simp only [attemptCost]; omega, ?_⟩
  have hpc : exitPc out.state =
      (if accepts description input certificate clock then (178 : Fin 185) else 115) := by
    by_cases h : out.state=0
    · simp [exitPc,accepts,c,out,h]
    · simp [exitPc,accepts,c,out,h]
  rw [← hpc]
  simpa only [attemptCost,c,out,Source284Relative.initial] using hall

/-- The candidate attempt is a trace of the embedded producer graph. -/
theorem embedded_attempt (b : Bank) (description input certificate clock : Nat) :
    let c := Source284Relative.initial input certificate
    let out := Source284Relative.run description c clock
    ((Grammar284ParseSource.parse Grammar284.SourceChars.source.toList).bind
      (fun g => Grammar284.coreGraph g 53)).bind
      (fun g => GraphExtendedTrace.graphTrace g
        (mapCfg ⟨50,regs b certificate input 1 description 0 0 clock⟩)
        (attemptCost description input certificate clock)) =
    some (⟨if accepts description input certificate clock then 178 else 115,
      swapBank (regs b out.left out.right out.state description 0 0 0)⟩,[]) := by
  dsimp only
  rw [Grammar284CoreTrace.embeddedGraph_run]
  have h := (attempt b description input certificate clock).2
  rw [h.1,h.2]

end Shared.Beeping.NPcoNP.Source284GraphCandidateAttempt
