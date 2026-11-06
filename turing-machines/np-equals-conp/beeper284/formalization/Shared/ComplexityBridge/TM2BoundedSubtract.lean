import Shared.ComplexityBridge.TM2BoundedUnary
import Shared.ComplexityBridge.TM2TapePairs
import Shared.ComplexityBridge.TM2FlattenList

set_option backward.isDefEq.respectTransparency false

/-! Saturating binary subtraction with an explicit unary size budget. Both
operands are truncated to the budget before subtraction, so the machine is
polynomial even when the binary inputs are much larger than the budget. -/
namespace Shared.ComplexityBridge.TM2BoundedSubtract
open Shared.ComplexityBridge

abbrev Input := List Bool × (Nat × Nat)

def keep (p : List Bool × Nat) : List Bool :=
  TM2ListMask.mask (!TM2BoundedWitnessGuard.guard p,[true])

theorem keep_isPolyTime : ComplexityTheory.IsPolyTime keep := by
  let flag : List Bool × Nat → Bool := fun p => !TM2BoundedWitnessGuard.guard p
  let one : List Bool × Nat → List Bool := fun _ => [true]
  let bit : List Bool × Nat → Bool := fun _ => true
  have hf : ComplexityTheory.IsPolyTime flag := TM2Compose.isPolyTime_comp TM2BoundedWitnessGuard.guard (fun b => !b)
    TM2BoundedWitnessGuard.guard_isPolyTime TM2GateDispatch.not_isPolyTime
  have hb : ComplexityTheory.IsPolyTime bit := TM2Constant.isPolyTime true
  have ho : ComplexityTheory.IsPolyTime one := TM2GateCNFPieces.singleton_isPolyTime bit hb
  have h := TM2Compose.isPolyTime_comp (fun p => (flag p,one p)) (TM2ListMask.mask (α := Bool))
    (TM2GuardAllStep.pair_isPolyTime flag one hf ho) TM2ListMask.mask_isPolyTime
  change ComplexityTheory.IsPolyTime keep at h
  exact h

def suffix (upper lower : List Bool) : List Bool :=
  (TM2ContextMapGeneric.contextMap keep (lower,TM2UnaryRange.rangeFromTokens upper)).flatten

theorem suffix_isPolyTime : ComplexityTheory.IsPolyTime (fun p : List Bool × List Bool => suffix p.1 p.2) := by
  let upper : List Bool × List Bool → List Bool := fun p => p.1
  let lower : List Bool × List Bool → List Bool := fun p => p.2
  let indices : List Bool × List Bool → List Nat := fun p => TM2UnaryRange.rangeFromTokens (upper p)
  let args : List Bool × List Bool → List Bool × List Nat := fun p => (lower p,indices p)
  let chunks : List Bool × List Bool → List (List Bool) := fun p => TM2ContextMapGeneric.contextMap keep (args p)
  have hu : ComplexityTheory.IsPolyTime upper := TM2PairFirst.first_isPolyTime
  have hl : ComplexityTheory.IsPolyTime lower := TM2GuardAllStep.second_isPolyTime
  have hi : ComplexityTheory.IsPolyTime indices := TM2Compose.isPolyTime_comp upper TM2UnaryRange.rangeFromTokens hu TM2UnaryRange.rangeFromTokens_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime lower indices hl hi
  have hc : ComplexityTheory.IsPolyTime chunks := TM2Compose.isPolyTime_comp args
    (TM2ContextMapGeneric.contextMap keep) ha (TM2ContextMapGeneric.contextMap_isPolyTime keep keep_isPolyTime)
  have h := TM2Compose.isPolyTime_comp chunks (List.flatten : List (List Bool) → List Bool) hc TM2FlattenList.flatten_isPolyTime
  change ComplexityTheory.IsPolyTime (fun p : List Bool × List Bool => suffix p.1 p.2) at h
  exact h

def suffixSpec (n k : Nat) : List Bool :=
  ((List.range n).map (fun i => if i < k then [] else [true])).flatten

theorem suffixSpec_correct (n k : Nat) : suffixSpec n k = List.replicate (n-k) true := by
  induction n generalizing k with
  | zero => simp [suffixSpec]
  | succ n ih =>
    cases k with
    | zero =>
      rw [suffixSpec,List.range_succ_eq_map]
      simp only [List.map_cons,List.map_map,Function.comp_def,not_lt_zero,if_false,List.flatten_cons]
      have hh := ih 0
      simp only [suffixSpec,Nat.sub_zero,not_lt_zero,if_false] at hh
      rw [hh]
      simp [List.replicate_succ]
    | succ k =>
      rw [suffixSpec,List.range_succ_eq_map]
      simp only [List.map_cons,List.map_map,Function.comp_def,Nat.zero_lt_succ,if_true,List.flatten_cons,List.nil_append,
        Nat.succ_lt_succ_iff]
      simpa [suffixSpec] using ih k

theorem suffix_correct (upper lower : List Bool) :
    suffix upper lower = List.replicate (upper.length-lower.length) true := by
  have he : suffix upper lower = suffixSpec upper.length lower.length := by
    simp [suffix,TM2ContextMapGeneric.contextMap,TM2UnaryRange.rangeFromTokens,keep,
      TM2TapePairs.guard_eq_decide,TM2ListMask.mask,suffixSpec]
    congr 1
    apply List.map_congr_left
    intro i _
    split_ifs <;> simp_all <;> omega
  rw [he,suffixSpec_correct]

def subtract (p : Input) : Nat :=
  (suffix (TM2BoundedUnary.expand (p.1,p.2.1)) (TM2BoundedUnary.expand (p.1,p.2.2))).length

theorem subtract_isPolyTime : ComplexityTheory.IsPolyTime subtract := by
  let budget : Input → List Bool := fun p => p.1
  let numbers : Input → Nat × Nat := fun p => p.2
  let x : Input → Nat := fun p => p.2.1
  let y : Input → Nat := fun p => p.2.2
  let upper : Input → List Bool := fun p => TM2BoundedUnary.expand (budget p,x p)
  let lower : Input → List Bool := fun p => TM2BoundedUnary.expand (budget p,y p)
  let args : Input → List Bool × List Bool := fun p => (upper p,lower p)
  let out : Input → List Bool := fun p => suffix (upper p) (lower p)
  have hb : ComplexityTheory.IsPolyTime budget := TM2PairFirst.first_isPolyTime
  have hn : ComplexityTheory.IsPolyTime numbers := TM2GuardAllStep.second_isPolyTime
  have hx : ComplexityTheory.IsPolyTime x := TM2Compose.isPolyTime_comp numbers (fun p : Nat × Nat => p.1) hn TM2PairFirst.first_isPolyTime
  have hy : ComplexityTheory.IsPolyTime y := TM2Compose.isPolyTime_comp numbers (fun p : Nat × Nat => p.2) hn TM2GuardAllStep.second_isPolyTime
  have hu : ComplexityTheory.IsPolyTime upper := TM2Compose.isPolyTime_comp (fun p => (budget p,x p)) TM2BoundedUnary.expand
    (TM2GuardAllStep.pair_isPolyTime budget x hb hx) TM2BoundedUnary.expand_isPolyTime
  have hl : ComplexityTheory.IsPolyTime lower := TM2Compose.isPolyTime_comp (fun p => (budget p,y p)) TM2BoundedUnary.expand
    (TM2GuardAllStep.pair_isPolyTime budget y hb hy) TM2BoundedUnary.expand_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime upper lower hu hl
  have hout : ComplexityTheory.IsPolyTime out := TM2Compose.isPolyTime_comp args (fun p : List Bool × List Bool => suffix p.1 p.2) ha suffix_isPolyTime
  have h := TM2Compose.isPolyTime_comp out List.length hout TM2BinaryListLength.length_isPolyTime
  change ComplexityTheory.IsPolyTime subtract at h
  exact h

theorem subtract_correct (tokens : List Bool) (x y : Nat) :
    subtract (tokens,(x,y)) = min x tokens.length - min y tokens.length := by
  simp [subtract,suffix_correct,TM2BoundedUnary.expand_correct]

theorem subtract_exact (tokens : List Bool) (x y : Nat) (hx : x ≤ tokens.length) (hy : y ≤ tokens.length) :
    subtract (tokens,(x,y)) = x-y := by
  simp [subtract_correct,Nat.min_eq_left hx,Nat.min_eq_left hy]

namespace Fixtures
example : subtract ([],(100,2)) = 0 := rfl
example : subtract ([true,true,true,true],(3,1)) = 2 := rfl
example : subtract ([true,true,true,true],(100,1)) = 3 := rfl
example : subtract ([true,true,true,true],(1,100)) = 0 := rfl
end Fixtures
end Shared.ComplexityBridge.TM2BoundedSubtract
