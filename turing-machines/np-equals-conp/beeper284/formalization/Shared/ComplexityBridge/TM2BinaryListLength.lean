import Shared.ComplexityBridge.TM2GateFoldLoop
import Shared.ComplexityBridge.TM2Constant

/-! Compute the length of any canonically encoded list as a binary natural.
The finite gate fold counts one step per element and charges its growing
state and output; no unit-cost integer assumption is used. -/
namespace Shared.ComplexityBridge.TM2BinaryListLength
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CircuitCNF

/-- The explicit gate encoding of a constant gate, as a tuple. -/
def constantCode (b : Bool) : TM2GateEncoding.Code := ((false,false),(b,(0,0)))

theorem constantCode_isPolyTime : ComplexityTheory.IsPolyTime constantCode := by
  let f : Bool → Bool := fun _ => false
  let z : Bool → Nat := fun _ => 0
  let idb : Bool → Bool := id
  let tags : Bool → Bool × Bool := fun b => (f b,f b)
  let numbers : Bool → Nat × Nat := fun b => (z b,z b)
  let payload : Bool → Bool × (Nat × Nat) := fun b => (idb b,numbers b)
  have hf : ComplexityTheory.IsPolyTime f := TM2Constant.isPolyTime false
  have hz : ComplexityTheory.IsPolyTime z := TM2EmptyConstant.zero_isPolyTime
  have hi : ComplexityTheory.IsPolyTime idb := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have ht : ComplexityTheory.IsPolyTime tags := TM2GuardAllStep.pair_isPolyTime f f hf hf
  have hn : ComplexityTheory.IsPolyTime numbers := TM2GuardAllStep.pair_isPolyTime z z hz hz
  have hp : ComplexityTheory.IsPolyTime payload := TM2GuardAllStep.pair_isPolyTime idb numbers hi hn
  have h := TM2GuardAllStep.pair_isPolyTime tags payload ht hp
  change ComplexityTheory.IsPolyTime (fun b : Bool => ((false,false),(b,(0,0))))
  exact h

/-- Reinterpreting the constructed tuple as a constant gate is free at the
machine boundary because their serialized bits agree exactly. -/
theorem constantGate_isPolyTime : ComplexityTheory.IsPolyTime Gate.constant := by
  obtain ⟨m⟩ := constantCode_isPolyTime
  refine ⟨{ toTM2ComputableAux := m.toTM2ComputableAux, time := m.time, outputsFun := ?_ }⟩
  intro b
  have h := m.outputsFun b
  have he : BitstringEncoding.bitEncode (Gate.constant b) = BitstringEncoding.bitEncode (constantCode b) := rfl
  change Turing.TM2OutputsInTime m.tm
    ((BitstringEncoding.bitEncode b).map m.inputAlphabet.symm)
    (some ((BitstringEncoding.bitEncode (Gate.constant b)).map m.outputAlphabet.symm))
    (m.time.eval (BitstringEncoding.bitEncode b).length)
  rw [he]
  exact h

/-- The result is the ordinary list length encoded in binary. -/
theorem length_isPolyTime {α : Type} [BitstringEncoding α] : ComplexityTheory.IsPolyTime
    (List.length : List α → Nat) := by
  let bit : α → Bool := fun _ => false
  let gate : α → Gate := fun _ => Gate.constant false
  let gs : List α → List Gate := fun xs => xs.map gate
  let zero : List α → Nat := fun _ => 0
  let request : List α → Nat × List Gate := fun xs => (zero xs,gs xs)
  let result : List α → Nat × CNF.Formula := fun xs => TM2GateFoldLoop.foldResult (request xs)
  have hb : ComplexityTheory.IsPolyTime bit := TM2Constant.isPolyTime false
  have hg : ComplexityTheory.IsPolyTime gate := TM2Compose.isPolyTime_comp bit Gate.constant hb constantGate_isPolyTime
  have hgs : ComplexityTheory.IsPolyTime gs := TM2ContextMapGeneric.listMap_isPolyTime gate hg
  have hz : ComplexityTheory.IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have hr : ComplexityTheory.IsPolyTime request := TM2GuardAllStep.pair_isPolyTime zero gs hz hgs
  have hresult : ComplexityTheory.IsPolyTime result := TM2Compose.isPolyTime_comp request TM2GateFoldLoop.foldResult hr TM2GateFoldLoop.foldResult_isPolyTime
  have h := TM2Compose.isPolyTime_comp result (fun p : Nat × CNF.Formula => p.1) hresult TM2PairFirst.first_isPolyTime
  have he : (fun xs => (result xs).1) = (List.length : List α → Nat) := by
    funext xs
    simp [result,request,zero,gs,TM2GateFoldLoop.foldResult]
  rw [he] at h
  exact h

namespace Fixtures
example : (List.length ([] : List Bool)) = 0 := rfl
example : (List.length [true,false,true]) = 3 := rfl
end Fixtures
end Shared.ComplexityBridge.TM2BinaryListLength
