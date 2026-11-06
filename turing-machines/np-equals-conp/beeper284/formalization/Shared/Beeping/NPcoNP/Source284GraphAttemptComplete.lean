import Shared.Beeping.NPcoNP.Source284GraphEvaluator

/-! Complete one bounded source attempt in the checked register graph,
including the zero-clock accept/reject dispatch. Supplied PC-50 register
banks are not a blank-start physical-table implementation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphAttemptComplete
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyRow
open Shared.Beeping.NPcoNP.Source284GraphApplyLoops
open Shared.Beeping.NPcoNP.Source284GraphPrepStep
open Shared.Beeping.NPcoNP.Source284GraphEvaluator
open Shared.Beeping.NPcoNP.Source284Relative
abbrev Bank := PASoundness.RegisterMachine.Bank 12

theorem row50_zero (b : Bank) (l r s d a w : Nat) :
    target.system.step ⟨50,regs b l r s d a w 0⟩ =
      (⟨85,regs b l r s d a w 0⟩,[]) := by rfl

theorem row85_zero (b : Bank) (l r d a w : Nat) :
    target.system.step ⟨85,regs b l r 0 d a w 0⟩ =
      (⟨87,regs b l r 0 d a w 0⟩,[]) := by rfl

theorem row85_positive (b : Bank) (l r s d a w : Nat) :
    target.system.step ⟨85,regs b l r (s+1) d a w 0⟩ =
      (⟨86,regs b l r s d a w 0⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write2]

theorem row86 (b : Bank) (l r s d a w : Nat) :
    target.system.step ⟨86,regs b l r s d a w 0⟩ =
      (⟨31,regs b l r (s+1) d a w 0⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write2]

def exitCost (s : Nat) : Nat := if s=0 then 2 else 3

def exitPc (s : Nat) : Fin 185 := if s=0 then 87 else 31

/-- The zero-clock dispatch preserves the complete represented source state.
State zero enters the accepting branch; any other state returns to the
certificate loop. -/
theorem exit (b : Bank) (l r s d : Nat) :
    Seg ⟨50,regs b l r s d 0 0 0⟩ ⟨exitPc s,regs b l r s d 0 0 0⟩ (exitCost s) := by
  cases s with
  | zero => simp [exitPc,exitCost,Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row50_zero,row85_zero]
  | succ s => simp [exitPc,exitCost,Seg,WordEventSystem.advance,WordEventSystem.wordFrom,
      row50_zero,row85_positive,row86]

def attemptCost (description input certificate clock : Nat) : Nat :=
  let c := Source284Relative.initial input certificate
  evalCost description c clock + exitCost (Source284Relative.run description c clock).state

/-- For every source description, input, certificate and finite clock, the
complete graph attempt terminates silently at the branch selected by the
existing `accepts` predicate. The exact final source tape is retained. -/
theorem attempt (b : Bank) (description input certificate clock : Nat) :
    let c := Source284Relative.initial input certificate
    let out := Source284Relative.run description c clock
    0 < attemptCost description input certificate clock ∧
    Seg ⟨50,regs b certificate input 1 description 0 0 clock⟩
      ⟨if accepts description input certificate clock then 87 else 31,
        regs b out.left out.right out.state description 0 0 0⟩
      (attemptCost description input certificate clock) := by
  let c := Source284Relative.initial input certificate
  let out := Source284Relative.run description c clock
  have he := evaluate b description c clock
  have hx := exit b out.left out.right out.state description
  have hall := cat he hx
  have hp : 0 < exitCost out.state := by unfold exitCost; split <;> decide
  have hp' : 0 < exitCost (Source284Relative.run description
      (Source284Relative.initial input certificate) clock).state := by
    simpa [out,c] using hp
  refine ⟨by simp only [attemptCost]; omega, ?_⟩
  have hpc : exitPc out.state =
      (if accepts description input certificate clock then (87 : Fin 185) else 31) := by
    by_cases h : out.state=0
    · simp [exitPc,accepts,c,out,h]
    · simp [exitPc,accepts,c,out,h]
  rw [← hpc]
  simpa only [attemptCost,c,out,Source284Relative.initial] using hall

/-- The same complete attempt is executed by the graph parsed from the
embedded grammar, with exactly the same empty event word. -/
theorem embedded_attempt (b : Bank) (description input certificate clock : Nat) :
    let c := Source284Relative.initial input certificate
    let out := Source284Relative.run description c clock
    ((Grammar284ParseSource.parse Grammar284.SourceChars.source.toList).bind
      (fun g => Grammar284.coreGraph g 53)).bind
      (fun g => GraphExtendedTrace.graphTrace g
        ⟨50,regs b certificate input 1 description 0 0 clock⟩
        (attemptCost description input certificate clock)) =
    some (⟨if accepts description input certificate clock then 87 else 31,
      regs b out.left out.right out.state description 0 0 0⟩,[]) := by
  dsimp only
  rw [Grammar284CoreTrace.embeddedGraph_run]
  have h := (attempt b description input certificate clock).2
  rw [h.1,h.2]

end Shared.Beeping.NPcoNP.Source284GraphAttemptComplete
