import Shared.ComplexityBridge.TM2BoundedUnary
import Shared.ComplexityBridge.TM2ListMask
import Shared.ComplexityBridge.TM2GateCNFPieces

/-! Build one unary token for each input position except the first, with
finite polynomial-time enumeration, comparison and list construction. -/
namespace Shared.ComplexityBridge.TM2UnaryPredecessor
open Shared.ComplexityBridge

def atIndex (n : Nat) : List Bool := TM2ListMask.mask (TM2BoundedWitnessGuard.numericNe (n,0),[true])

theorem atIndex_isPolyTime : ComplexityTheory.IsPolyTime atIndex := by
  let index : Nat → Nat := id
  let zero : Nat → Nat := fun _ => 0
  let args : Nat → Nat × Nat := fun n => (index n,zero n)
  let flag : Nat → Bool := fun n => TM2BoundedWitnessGuard.numericNe (args n)
  let bit : Nat → Bool := fun _ => true
  let one : Nat → List Bool := fun n => [bit n]
  have hi : ComplexityTheory.IsPolyTime index := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hz : ComplexityTheory.IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime index zero hi hz
  have hf : ComplexityTheory.IsPolyTime flag := TM2Compose.isPolyTime_comp args TM2BoundedWitnessGuard.numericNe ha TM2BoundedWitnessGuard.numericNe_isPolyTime
  have hb : ComplexityTheory.IsPolyTime bit := TM2Constant.isPolyTime true
  have ho : ComplexityTheory.IsPolyTime one := TM2GateCNFPieces.singleton_isPolyTime bit hb
  have hp := TM2GuardAllStep.pair_isPolyTime flag one hf ho
  have h := TM2Compose.isPolyTime_comp (fun n => (flag n,one n)) (TM2ListMask.mask (α := Bool)) hp TM2ListMask.mask_isPolyTime
  change ComplexityTheory.IsPolyTime (fun n : Nat => TM2ListMask.mask (TM2BoundedWitnessGuard.numericNe (n,0),[true]))
  exact h

def predecessor (xs : List Bool) : List Bool := ((List.range xs.length).map atIndex).flatten

theorem predecessor_isPolyTime : ComplexityTheory.IsPolyTime predecessor := by
  have hm := TM2ContextMapGeneric.listMap_isPolyTime atIndex atIndex_isPolyTime
  have h := TM2Compose.isPolyTime_comp TM2UnaryRange.rangeFromTokens (fun xs : List Nat => xs.map atIndex)
    TM2UnaryRange.rangeFromTokens_isPolyTime hm
  have hc := TM2Compose.isPolyTime_comp (fun xs => (TM2UnaryRange.rangeFromTokens xs).map atIndex)
    (List.flatten : List (List Bool) → List Bool) h TM2FlattenList.flatten_isPolyTime
  change ComplexityTheory.IsPolyTime (fun xs : List Bool => ((List.range xs.length).map atIndex).flatten)
  exact hc

theorem range_predecessor (n : Nat) :
    ((List.range n).map atIndex).flatten = List.replicate (n-1) true := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [List.range_succ_eq_map]
    simp [atIndex,TM2ListMask.mask,TM2BoundedWitnessGuard.numericNe,List.map_map,Function.comp_def]

theorem predecessor_correct (xs : List Bool) : predecessor xs = List.replicate (xs.length-1) true :=
  range_predecessor xs.length

namespace Fixtures
example : predecessor [] = [] := rfl
example : predecessor [false] = [] := rfl
example : predecessor [false,true,false] = [true,true] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2UnaryPredecessor
