import Shared.ComplexityBridge.TM2ProgramUnroll
import Shared.ComplexityBridge.TM2TapeWorker

set_option backward.isDefEq.respectTransparency false

/-! Build the actual bounded acceptance circuit before its final witness-wire
relocation. Public input, witness count and clock are explicitly supplied. -/
namespace Shared.ComplexityBridge.TM2BoundedCircuitWorker
open Shared.ComplexityBridge
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTotalize

abbrev Input := TM2CircuitOutputWorker.Input

def args (z : Input) : TM2ProgramUnroll.Input := (TM2CircuitOutputWorker.windowTokens z,z.2)
def gates (program : Program) (z : Input) : List CircuitCNF.Gate := TM2ProgramUnroll.gates (totalProgram program) (args z)
def refs (program : Program) (z : Input) : List Nat := TM2ProgramUnroll.refs (totalProgram program) (args z)

theorem args_isPolyTime : ComplexityTheory.IsPolyTime args := by
  have h := TM2GuardAllStep.pair_isPolyTime TM2CircuitOutputWorker.windowTokens (fun z : Input => z.2)
    TM2TapeWorker.windowTokens_isPolyTime TM2GuardAllStep.second_isPolyTime
  exact h

theorem workers_isPolyTime (program : Program) : ComplexityTheory.IsPolyTime (gates program) ∧ ComplexityTheory.IsPolyTime (refs program) :=
  ⟨TM2Compose.isPolyTime_comp args (TM2ProgramUnroll.gates (totalProgram program)) args_isPolyTime (TM2ProgramUnroll.workers_isPolyTime _).1,
   TM2Compose.isPolyTime_comp args (TM2ProgramUnroll.refs (totalProgram program)) args_isPolyTime (TM2ProgramUnroll.workers_isPolyTime _).2⟩

theorem workers_correct (program : Program) (pub witness fuel : List Bool) :
    let input := CircuitWitness.dummyInput pub (3*witness.length)
    let width := CircuitBounded.circuitWidth program input fuel.length
    let gs := CircuitBounded.updateGates program input fuel.length
    let outs := CircuitBounded.updateOutputs program input fuel.length
    gates program ((pub,witness),fuel) = CircuitBounded.circuitGates program input fuel.length ∧
    refs program ((pub,witness),fuel) = CircuitRelocate.finalRefs width gs outs width (List.range width) fuel.length := by
  have h := TM2ProgramUnroll.workers_correct (totalProgram program)
    (TM2CircuitOutputWorker.windowTokens ((pub,witness),fuel)) fuel
  have hw : (TM2CircuitOutputWorker.windowTokens ((pub,witness),fuel)).length =
      CircuitBounded.window (CircuitWitness.dummyInput pub (3*witness.length)) fuel.length := by
    simp [TM2CircuitOutputWorker.windowTokens,TM2CircuitOutputWorker.countTokens,
      TM2CircuitOutputWorker.copies_length,CircuitBounded.window,CircuitWitness.dummyInput,Nat.add_assoc]
  simp only [hw] at h
  simpa [gates,refs,args,CircuitBounded.circuitGates,CircuitBounded.updateGates,
    CircuitBounded.updateOutputs,CircuitBounded.circuitWidth] using h

namespace Fixtures
example : gates [] (([],[]),[]) = [] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2BoundedCircuitWorker
