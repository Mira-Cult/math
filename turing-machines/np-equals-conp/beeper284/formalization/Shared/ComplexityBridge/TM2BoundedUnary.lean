import Shared.ComplexityBridge.TM2TruePrefix
import Shared.ComplexityBridge.TM2BoundedWitnessGuard
import Shared.ComplexityBridge.TM2ShapeClauses

/-! Expand a binary witness length only up to an explicit unary budget. -/
namespace Shared.ComplexityBridge.TM2BoundedUnary
open Shared.ComplexityBridge

/-- The output has `min n budget.length` true tokens, even when the binary
number exceeds the budget. No output length can exceed the unary input. -/
def expand (p : List Bool × Nat) : List Bool :=
  TM2TruePrefix.truePrefix ((List.range p.1.length).map (fun i => TM2BoundedWitnessGuard.numericNe (p.2,i)))

theorem count_range (budget n : Nat) :
    TM2TruePrefix.count ((List.range budget).map (fun i => TM2BoundedWitnessGuard.numericNe (n,i))) = min n budget := by
  induction budget generalizing n with
  | zero => simp [TM2TruePrefix.count]
  | succ budget ih =>
    rw [List.range_succ_eq_map]
    cases n with
    | zero => simp [TM2TruePrefix.count,TM2BoundedWitnessGuard.numericNe]
    | succ n =>
      simp only [List.map_cons,List.map_map,Function.comp_def,TM2TruePrefix.count]
      simpa [TM2BoundedWitnessGuard.numericNe,Nat.succ_min_succ] using ih n

theorem expand_correct (tokens : List Bool) (n : Nat) :
    expand (tokens,n) = List.replicate (min n tokens.length) true := by
  simp [expand,TM2TruePrefix.truePrefix,count_range]

theorem expand_isPolyTime : ComplexityTheory.IsPolyTime expand := by
  let tokens : List Bool × Nat → List Bool := fun p => p.1
  let value : List Bool × Nat → Nat := fun p => p.2
  let indices : List Bool × Nat → List Nat := fun p => TM2UnaryRange.rangeFromTokens (tokens p)
  let args : List Bool × Nat → Nat × List Nat := fun p => (value p,indices p)
  let tests : List Bool × Nat → List Bool := fun p => TM2ContextMapGeneric.contextMap TM2BoundedWitnessGuard.numericNe (args p)
  have ht : ComplexityTheory.IsPolyTime tokens := TM2PairFirst.first_isPolyTime
  have hv : ComplexityTheory.IsPolyTime value := TM2GuardAllStep.second_isPolyTime
  have hi : ComplexityTheory.IsPolyTime indices := TM2Compose.isPolyTime_comp tokens TM2UnaryRange.rangeFromTokens ht TM2UnaryRange.rangeFromTokens_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime value indices hv hi
  have hm := TM2ContextMapGeneric.contextMap_isPolyTime TM2BoundedWitnessGuard.numericNe TM2BoundedWitnessGuard.numericNe_isPolyTime
  have hx : ComplexityTheory.IsPolyTime tests := TM2Compose.isPolyTime_comp args (TM2ContextMapGeneric.contextMap TM2BoundedWitnessGuard.numericNe) ha hm
  have h := TM2Compose.isPolyTime_comp tests TM2TruePrefix.truePrefix hx TM2TruePrefix.prefix_isPolyTime
  change ComplexityTheory.IsPolyTime (fun p : List Bool × Nat =>
    TM2TruePrefix.truePrefix ((List.range p.1.length).map (fun i => TM2BoundedWitnessGuard.numericNe (p.2,i))))
  simpa [tests,args,value,indices,tokens,TM2ContextMapGeneric.contextMap,TM2UnaryRange.rangeFromTokens] using h

/-- Under the generator guard the adapter outputs exactly `n` unary tokens. -/
theorem expand_guarded (tokens : List Bool) (n : Nat) (h : n < tokens.length) :
    expand (tokens,n) = List.replicate n true := by
  rw [expand_correct,Nat.min_eq_left (Nat.le_of_lt h)]

def shape (p : Nat × (List Bool × Nat)) : CNF.Formula :=
  TM2ShapeClauses.fromTokens (p.1,expand p.2)

theorem shape_isPolyTime : ComplexityTheory.IsPolyTime shape := by
  let base : Nat × (List Bool × Nat) → Nat := fun p => p.1
  let args : Nat × (List Bool × Nat) → List Bool × Nat := fun p => p.2
  let tokens : Nat × (List Bool × Nat) → List Bool := fun p => expand (args p)
  let request : Nat × (List Bool × Nat) → Nat × List Bool := fun p => (base p,tokens p)
  have hb : ComplexityTheory.IsPolyTime base := TM2PairFirst.first_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.second_isPolyTime
  have ht : ComplexityTheory.IsPolyTime tokens := TM2Compose.isPolyTime_comp args expand ha expand_isPolyTime
  have hr : ComplexityTheory.IsPolyTime request := TM2GuardAllStep.pair_isPolyTime base tokens hb ht
  have h := TM2Compose.isPolyTime_comp request TM2ShapeClauses.fromTokens hr TM2ShapeClauses.fromTokens_isPolyTime
  change ComplexityTheory.IsPolyTime (fun p : Nat × (List Bool × Nat) => TM2ShapeClauses.fromTokens (p.1,expand p.2))
  exact h

theorem shape_guarded (base : Nat) (tokens : List Bool) (n : Nat) (h : n < tokens.length) :
    shape (base,(tokens,n)) = CircuitPairWitness.shapeClauses base n := by
  simp [shape,TM2ShapeClauses.fromTokens_correct,expand_guarded tokens n h]

namespace Fixtures
example : expand ([],0) = [] := rfl
example : expand ([false,true,true],2) = [true,true] := rfl
example : expand ([false,true],5) = [true,true] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2BoundedUnary
