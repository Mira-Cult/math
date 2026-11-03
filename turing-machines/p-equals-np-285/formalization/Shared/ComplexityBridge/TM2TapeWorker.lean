import Shared.ComplexityBridge.TM2TapeMove
import Shared.ComplexityBridge.TM2CircuitOutputWorker

set_option backward.isDefEq.respectTransparency false

/-! Bind the unary-window movement generator to the actual bounded-circuit
input parameters used by the witness circuit. -/
namespace Shared.ComplexityBridge.TM2TapeWorker
open Shared.ComplexityBridge
open Shared.ComplexityBridge.TM2CircuitOutputWorker

abbrev Input := TM2CircuitOutputWorker.Input

theorem windowTokens_isPolyTime : ComplexityTheory.IsPolyTime windowTokens := by
  let pair : Input → List Bool × List Bool := fun z => z.1
  let pub : Input → List Bool := fun z => z.1.1
  let witness : Input → List Bool := fun z => z.1.2
  let fuel : Input → List Bool := fun z => z.2
  let count : Input → List Bool := countTokens
  have hp : ComplexityTheory.IsPolyTime pair := TM2PairFirst.first_isPolyTime
  have hpub : ComplexityTheory.IsPolyTime pub := TM2Compose.isPolyTime_comp pair
    (fun p : List Bool × List Bool => p.1) hp TM2PairFirst.first_isPolyTime
  have hw : ComplexityTheory.IsPolyTime witness := TM2Compose.isPolyTime_comp pair
    (fun p : List Bool × List Bool => p.2) hp TM2GuardAllStep.second_isPolyTime
  have hf : ComplexityTheory.IsPolyTime fuel := TM2GuardAllStep.second_isPolyTime
  have hc : ComplexityTheory.IsPolyTime count := TM2Compose.isPolyTime_comp witness (copies 3) hw (copies_isPolyTime 3)
  have h := TM2CircuitTemplate.append_isPolyTime (fun z => pub z ++ count z) fuel
    (TM2CircuitTemplate.append_isPolyTime pub count hpub hc) hf
  change ComplexityTheory.IsPolyTime windowTokens at h
  exact h

def worker (z : Input) : List CircuitCNF.Gate := TM2TapeMove.moveGates (windowTokens z)

theorem worker_isPolyTime : ComplexityTheory.IsPolyTime worker :=
  TM2Compose.isPolyTime_comp windowTokens TM2TapeMove.moveGates windowTokens_isPolyTime TM2TapeMove.moveGates_isPolyTime

/-- The generated gates are exactly the tape movement component of the
bounded circuit for the public bits, witness count, and clock. -/
theorem worker_correct (pub witness fuel : List Bool) :
    worker ((pub,witness),fuel) = CircuitTapeMove.moveGates
      (CircuitBounded.window (CircuitWitness.dummyInput pub (3*witness.length)) fuel.length) := by
  simp [worker,TM2TapeMove.moveGates,windowTokens,countTokens,copies_length,
    CircuitBounded.window,CircuitWitness.dummyInput,Nat.add_assoc]

namespace Fixtures
example : worker (([],[]),[]) = CircuitTapeMove.moveGates 0 := rfl
end Fixtures
end Shared.ComplexityBridge.TM2TapeWorker
