import Shared.ComplexityBridge.TM2BoundedSubtract
import Shared.ComplexityBridge.TM2If
import Shared.ComplexityBridge.TM2ContextMapGeneric
import Shared.ComplexityBridge.CircuitWitness
import Shared.ComplexityBridge.TM2CircuitTemplate

set_option backward.isDefEq.respectTransparency false

/-! Generate witness-patch wire references using explicitly charged unary
width, start and count. All branches are total on arbitrary token lists. -/
namespace Shared.ComplexityBridge.TM2PatchRefs
open Shared.ComplexityBridge

abbrev Context := List Bool × (List Bool × List Bool)
abbrev Entry := Context × Nat

def entry (p : Entry) : Nat :=
  let width := p.1.1
  let start := p.1.2.1
  let count := p.1.2.2
  let index := p.2
  if !TM2BoundedWitnessGuard.guard (start,index) && TM2BoundedWitnessGuard.guard (start++count,index) then
    width.length+TM2BoundedSubtract.subtract (width,(index,start.length))
  else index

theorem entry_isPolyTime : ComplexityTheory.IsPolyTime entry := by
  let ctx : Entry → Context := fun p => p.1
  let index : Entry → Nat := fun p => p.2
  let width : Entry → List Bool := fun p => p.1.1
  let tail : Entry → List Bool × List Bool := fun p => p.1.2
  let start : Entry → List Bool := fun p => p.1.2.1
  let count : Entry → List Bool := fun p => p.1.2.2
  let endpoint : Entry → List Bool := fun p => start p++count p
  let lower : Entry → Bool := fun p => TM2BoundedWitnessGuard.guard (start p,index p)
  let upper : Entry → Bool := fun p => TM2BoundedWitnessGuard.guard (endpoint p,index p)
  let notLower : Entry → Bool := fun p => !lower p
  let flag : Entry → Bool := fun p => notLower p && upper p
  let widthLen : Entry → Nat := fun p => (width p).length
  let startLen : Entry → Nat := fun p => (start p).length
  let diff : Entry → Nat := fun p => TM2BoundedSubtract.subtract (width p,(index p,startLen p))
  let yes : Entry → Nat := fun p => widthLen p+diff p
  have hc : ComplexityTheory.IsPolyTime ctx := TM2PairFirst.first_isPolyTime
  have hi : ComplexityTheory.IsPolyTime index := TM2GuardAllStep.second_isPolyTime
  have hw : ComplexityTheory.IsPolyTime width := TM2Compose.isPolyTime_comp ctx (fun p : Context => p.1) hc TM2PairFirst.first_isPolyTime
  have ht : ComplexityTheory.IsPolyTime tail := TM2Compose.isPolyTime_comp ctx (fun p : Context => p.2) hc TM2GuardAllStep.second_isPolyTime
  have hs : ComplexityTheory.IsPolyTime start := TM2Compose.isPolyTime_comp tail (fun p : List Bool × List Bool => p.1) ht TM2PairFirst.first_isPolyTime
  have hcount : ComplexityTheory.IsPolyTime count := TM2Compose.isPolyTime_comp tail (fun p : List Bool × List Bool => p.2) ht TM2GuardAllStep.second_isPolyTime
  have he : ComplexityTheory.IsPolyTime endpoint := TM2CircuitTemplate.append_isPolyTime start count hs hcount
  have hlo : ComplexityTheory.IsPolyTime lower := TM2Compose.isPolyTime_comp (fun p => (start p,index p)) TM2BoundedWitnessGuard.guard
    (TM2GuardAllStep.pair_isPolyTime start index hs hi) TM2BoundedWitnessGuard.guard_isPolyTime
  have hup : ComplexityTheory.IsPolyTime upper := TM2Compose.isPolyTime_comp (fun p => (endpoint p,index p)) TM2BoundedWitnessGuard.guard
    (TM2GuardAllStep.pair_isPolyTime endpoint index he hi) TM2BoundedWitnessGuard.guard_isPolyTime
  have hn : ComplexityTheory.IsPolyTime notLower := TM2Compose.isPolyTime_comp lower (fun b => !b) hlo TM2GateDispatch.not_isPolyTime
  have hf : ComplexityTheory.IsPolyTime flag := TM2Compose.isPolyTime_comp (fun p => (notLower p,upper p)) (fun p : Bool × Bool => p.1 && p.2)
    (TM2GuardAllStep.pair_isPolyTime notLower upper hn hup) TM2GateDispatch.and_isPolyTime
  have hwl : ComplexityTheory.IsPolyTime widthLen := TM2Compose.isPolyTime_comp width List.length hw TM2BinaryListLength.length_isPolyTime
  have hsl : ComplexityTheory.IsPolyTime startLen := TM2Compose.isPolyTime_comp start List.length hs TM2BinaryListLength.length_isPolyTime
  have hd : ComplexityTheory.IsPolyTime diff := TM2Compose.isPolyTime_comp (fun p => (width p,(index p,startLen p))) TM2BoundedSubtract.subtract
    (TM2GuardAllStep.pair_isPolyTime width (fun p => (index p,startLen p)) hw (TM2GuardAllStep.pair_isPolyTime index startLen hi hsl))
    TM2BoundedSubtract.subtract_isPolyTime
  have hy : ComplexityTheory.IsPolyTime yes := TM2Compose.isPolyTime_comp (fun p => (widthLen p,diff p)) CNFBinaryPairAdd.addPair
    (TM2GuardAllStep.pair_isPolyTime widthLen diff hwl hd) CNFBinaryPairAdd.addPair_isPolyTime
  have h := TM2If.if_isPolyTime flag yes index hf hy hi
  change ComplexityTheory.IsPolyTime entry at h
  exact h

theorem entry_correct (width start count : List Bool) (index : Nat)
    (hs : start.length ≤ width.length) (hi : index ≤ width.length) :
    entry ((width,(start,count)),index) =
      (if start.length ≤ index ∧ index < start.length+count.length then width.length+(index-start.length) else index) := by
  simp [entry,TM2TapePairs.guard_eq_decide,TM2BoundedSubtract.subtract_exact width index start.length hi hs]

def patch (p : Context) : List Nat :=
  TM2ContextMapGeneric.contextMap entry (p,TM2UnaryRange.rangeFromTokens p.1)

theorem patch_isPolyTime : ComplexityTheory.IsPolyTime patch := by
  let ident : Context → Context := id
  let width : Context → List Bool := fun p => p.1
  let indices : Context → List Nat := fun p => TM2UnaryRange.rangeFromTokens (width p)
  let args : Context → Context × List Nat := fun p => (ident p,indices p)
  have hid : ComplexityTheory.IsPolyTime ident := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hw : ComplexityTheory.IsPolyTime width := TM2PairFirst.first_isPolyTime
  have hi : ComplexityTheory.IsPolyTime indices := TM2Compose.isPolyTime_comp width TM2UnaryRange.rangeFromTokens hw TM2UnaryRange.rangeFromTokens_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime ident indices hid hi
  have h := TM2Compose.isPolyTime_comp args (TM2ContextMapGeneric.contextMap entry) ha
    (TM2ContextMapGeneric.contextMap_isPolyTime entry entry_isPolyTime)
  change ComplexityTheory.IsPolyTime patch at h
  exact h

theorem patch_correct (width start count : List Bool) (hs : start.length ≤ width.length) :
    patch (width,(start,count)) = CircuitWitness.patchRefs width.length start.length count.length := by
  unfold patch TM2ContextMapGeneric.contextMap TM2UnaryRange.rangeFromTokens CircuitWitness.patchRefs
  apply List.map_congr_left
  intro i hi
  have hb : i ≤ width.length := by simpa using Nat.le_of_lt (List.mem_range.mp hi)
  exact entry_correct width start count i hs hb

namespace Fixtures
example : patch ([true,true,true,true],([true],[true,true])) = [0,4,5,3] := rfl
example : patch ([],([],[])) = [] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2PatchRefs
