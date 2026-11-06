import Shared.ComplexityBridge.TM2TapePairs
import Shared.ComplexityBridge.TM2MuxList
import Shared.ComplexityBridge.TM2ContextMapGeneric
import Shared.ComplexityBridge.TM2UnaryRange

set_option backward.isDefEq.respectTransparency false

/-! Construct the exact movement circuit from unary window tokens. -/
namespace Shared.ComplexityBridge.TM2TapeMove
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CircuitCNF

def indices (tokens : List Bool) : List Nat :=
  TM2UnaryRange.rangeFromTokens (tokens++tokens++[true])

theorem indices_isPolyTime : ComplexityTheory.IsPolyTime indices := by
  let idb : List Bool → List Bool := id
  let oneBit : List Bool → Bool := fun _ => true
  let one : List Bool → List Bool := fun _ => [true]
  let twice : List Bool → List Bool := fun x => x++x
  let total : List Bool → List Bool := fun x => twice x++one x
  have hi : ComplexityTheory.IsPolyTime idb := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hb : ComplexityTheory.IsPolyTime oneBit := TM2Constant.isPolyTime true
  have ho : ComplexityTheory.IsPolyTime one := TM2GateCNFPieces.singleton_isPolyTime oneBit hb
  have hd : ComplexityTheory.IsPolyTime twice := TM2Compose.isPolyTime_comp (fun x => (idb x,idb x))
    (TM2ListAppend.append (α := Bool)) (TM2GuardAllStep.pair_isPolyTime idb idb hi hi) TM2ListAppend.append_isPolyTime
  have ht : ComplexityTheory.IsPolyTime total := TM2Compose.isPolyTime_comp (fun x => (twice x,one x))
    (TM2ListAppend.append (α := Bool)) (TM2GuardAllStep.pair_isPolyTime twice one hd ho) TM2ListAppend.append_isPolyTime
  have h := TM2Compose.isPolyTime_comp total TM2UnaryRange.rangeFromTokens ht TM2UnaryRange.rangeFromTokens_isPolyTime
  change ComplexityTheory.IsPolyTime indices at h
  exact h

def pairs (tokens : List Bool) : List (Nat × Nat) :=
  TM2ContextMapGeneric.contextMap TM2TapePairs.pairAt (tokens,indices tokens)

theorem pairs_correct (tokens : List Bool) : pairs tokens = CircuitTapeMove.pairs tokens.length := by
  simp [pairs,TM2ContextMapGeneric.contextMap,indices,TM2UnaryRange.rangeFromTokens,
    CircuitTapeMove.pairs,TM2TapePairs.pairAt_correct, Nat.mul_comm]
  congr 2 <;> omega

theorem pairs_isPolyTime : ComplexityTheory.IsPolyTime pairs := by
  let idb : List Bool → List Bool := id
  let arg : List Bool → List Bool × List Nat := fun x => (x,indices x)
  have hi : ComplexityTheory.IsPolyTime idb := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have ha : ComplexityTheory.IsPolyTime arg := TM2GuardAllStep.pair_isPolyTime idb indices hi indices_isPolyTime
  have h := TM2Compose.isPolyTime_comp arg (TM2ContextMapGeneric.contextMap TM2TapePairs.pairAt) ha
    (TM2ContextMapGeneric.contextMap_isPolyTime TM2TapePairs.pairAt TM2TapePairs.pairAt_isPolyTime)
  change ComplexityTheory.IsPolyTime pairs at h
  exact h

def moveGates (tokens : List Bool) : List Gate := CircuitTapeMove.moveGates tokens.length

/-- The exact movement gate list is produced in polynomial time in the full
canonical encoding of the unary window; no binary number is silently expanded. -/
theorem moveGates_isPolyTime : ComplexityTheory.IsPolyTime moveGates := by
  let n : List Bool → Nat := List.length
  let twice : List Bool → Nat := fun x => 2*n x
  let base : List Bool → Nat := fun x => twice x+4
  let zero : List Bool → Nat := fun _ => 0
  let one : List Bool → Nat := fun x => zero x+1
  let ctx : List Bool → Nat × Nat := fun x => (base x,one x)
  let args : List Bool → TM2MuxList.Request := fun x => (ctx x,pairs x)
  let body : List Bool → List Gate := fun x => TM2MuxList.muxList (args x)
  let falseBit : List Bool → Bool := fun _ => false
  let falseGate : List Bool → Gate := fun _ => Gate.constant false
  let header : List Bool → List Gate := fun _ => [Gate.constant false]
  have hn : ComplexityTheory.IsPolyTime n := TM2BinaryListLength.length_isPolyTime
  have hd : ComplexityTheory.IsPolyTime twice := TM2Compose.isPolyTime_comp n (fun x => 2*x) hn CNFBinaryIndex.double_isPolyTime
  have hb : ComplexityTheory.IsPolyTime base := TM2Compose.isPolyTime_comp twice (fun x => x+4) hd (TM2FixedRows.addFixed_isPolyTime 4)
  have hz : ComplexityTheory.IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have ho : ComplexityTheory.IsPolyTime one := TM2Compose.isPolyTime_comp zero (fun x => x+1) hz (TM2FixedRows.addFixed_isPolyTime 1)
  have hc : ComplexityTheory.IsPolyTime ctx := TM2GuardAllStep.pair_isPolyTime base one hb ho
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime ctx pairs hc pairs_isPolyTime
  have hbody : ComplexityTheory.IsPolyTime body := TM2Compose.isPolyTime_comp args TM2MuxList.muxList ha TM2MuxList.muxList_isPolyTime
  have hf : ComplexityTheory.IsPolyTime falseBit := TM2Constant.isPolyTime false
  have hg : ComplexityTheory.IsPolyTime falseGate := TM2Compose.isPolyTime_comp falseBit Gate.constant hf TM2BinaryListLength.constantGate_isPolyTime
  have hh : ComplexityTheory.IsPolyTime header := TM2GateCNFPieces.singleton_isPolyTime falseGate hg
  have h := TM2RowGates.append_isPolyTime header body hh hbody
  have he : (fun x => header x++body x) = moveGates := by
    funext x
    simp only [header,body,args,ctx,base,twice,n,one,zero,TM2MuxList.muxList,pairs_correct,
      moveGates,CircuitTapeMove.moveGates,CircuitTapeMove.width]
    congr 2 <;> omega
  rw [he] at h
  exact h

namespace Fixtures
example : pairs [] = [(3,3)] := rfl
example : moveGates [] = [.constant false,.neg 1,.conj 1 3,.conj 4 3,.disj 5 6] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2TapeMove
