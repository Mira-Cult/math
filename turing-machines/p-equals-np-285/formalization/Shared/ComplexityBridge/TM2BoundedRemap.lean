import Shared.ComplexityBridge.TM2ListLookup
import Shared.ComplexityBridge.TM2BoundedSubtract
import Shared.ComplexityBridge.TM2If
import Shared.ComplexityBridge.CircuitRelocate

set_option backward.isDefEq.respectTransparency false

/-! A total, charged wire-relocation operation with an explicit unary budget.
It agrees with the circuit semantics whenever width and index fit the budget. -/
namespace Shared.ComplexityBridge.TM2BoundedRemap
open Shared.ComplexityBridge

abbrev Input := List Bool × ((Nat × Nat) × (List Nat × Nat))

def remap (p : Input) : Nat :=
  let budget := p.1
  let width := p.2.1.1
  let base := p.2.1.2
  let refs := p.2.2.1
  let index := p.2.2.2
  if TM2BoundedWitnessGuard.guard (TM2BoundedUnary.expand (budget,width),index) then
    (refs[index]?).getD 0
  else base + TM2BoundedSubtract.subtract (budget,(index,width))

/-- The bounded worker is total on all inputs and its clock charges the
entire encoded request. -/
theorem remap_isPolyTime : ComplexityTheory.IsPolyTime remap := by
  let budget : Input → List Bool := fun p => p.1
  let rest : Input → (Nat × Nat) × (List Nat × Nat) := fun p => p.2
  let dims : Input → Nat × Nat := fun p => p.2.1
  let tail : Input → List Nat × Nat := fun p => p.2.2
  let width : Input → Nat := fun p => p.2.1.1
  let base : Input → Nat := fun p => p.2.1.2
  let refs : Input → List Nat := fun p => p.2.2.1
  let index : Input → Nat := fun p => p.2.2.2
  let tokens : Input → List Bool := fun p => TM2BoundedUnary.expand (budget p,width p)
  let flag : Input → Bool := fun p => TM2BoundedWitnessGuard.guard (tokens p,index p)
  let yes : Input → Nat := fun p => ((refs p)[index p]?).getD 0
  let diff : Input → Nat := fun p => TM2BoundedSubtract.subtract (budget p,(index p,width p))
  let no : Input → Nat := fun p => base p+diff p
  have hb : ComplexityTheory.IsPolyTime budget := TM2PairFirst.first_isPolyTime
  have hr : ComplexityTheory.IsPolyTime rest := TM2GuardAllStep.second_isPolyTime
  have hd : ComplexityTheory.IsPolyTime dims := TM2Compose.isPolyTime_comp rest
    (fun p : (Nat × Nat) × (List Nat × Nat) => p.1) hr TM2PairFirst.first_isPolyTime
  have ht : ComplexityTheory.IsPolyTime tail := TM2Compose.isPolyTime_comp rest
    (fun p : (Nat × Nat) × (List Nat × Nat) => p.2) hr TM2GuardAllStep.second_isPolyTime
  have hw : ComplexityTheory.IsPolyTime width := TM2Compose.isPolyTime_comp dims (fun p : Nat × Nat => p.1) hd TM2PairFirst.first_isPolyTime
  have hbase : ComplexityTheory.IsPolyTime base := TM2Compose.isPolyTime_comp dims (fun p : Nat × Nat => p.2) hd TM2GuardAllStep.second_isPolyTime
  have hrefs : ComplexityTheory.IsPolyTime refs := TM2Compose.isPolyTime_comp tail (fun p : List Nat × Nat => p.1) ht TM2PairFirst.first_isPolyTime
  have hi : ComplexityTheory.IsPolyTime index := TM2Compose.isPolyTime_comp tail (fun p : List Nat × Nat => p.2) ht TM2GuardAllStep.second_isPolyTime
  have htok : ComplexityTheory.IsPolyTime tokens := TM2Compose.isPolyTime_comp (fun p => (budget p,width p)) TM2BoundedUnary.expand
    (TM2GuardAllStep.pair_isPolyTime budget width hb hw) TM2BoundedUnary.expand_isPolyTime
  have hf : ComplexityTheory.IsPolyTime flag := TM2Compose.isPolyTime_comp (fun p => (tokens p,index p)) TM2BoundedWitnessGuard.guard
    (TM2GuardAllStep.pair_isPolyTime tokens index htok hi) TM2BoundedWitnessGuard.guard_isPolyTime
  have hy : ComplexityTheory.IsPolyTime yes := TM2Compose.isPolyTime_comp (fun p => (refs p,index p))
    (fun p : List Nat × Nat => (p.1[p.2]?).getD 0)
    (TM2GuardAllStep.pair_isPolyTime refs index hrefs hi) TM2ListLookup.naturalGet_isPolyTime
  have hdiff : ComplexityTheory.IsPolyTime diff := TM2Compose.isPolyTime_comp (fun p => (budget p,(index p,width p)))
    TM2BoundedSubtract.subtract (TM2GuardAllStep.pair_isPolyTime budget (fun p => (index p,width p)) hb
      (TM2GuardAllStep.pair_isPolyTime index width hi hw)) TM2BoundedSubtract.subtract_isPolyTime
  have hn : ComplexityTheory.IsPolyTime no := TM2Compose.isPolyTime_comp (fun p => (base p,diff p)) CNFBinaryPairAdd.addPair
    (TM2GuardAllStep.pair_isPolyTime base diff hbase hdiff) CNFBinaryPairAdd.addPair_isPolyTime
  have h := TM2If.if_isPolyTime flag yes no hf hy hn
  change ComplexityTheory.IsPolyTime remap at h
  exact h

theorem remap_correct (budget : List Bool) (width base : Nat) (refs : List Nat) (index : Nat)
    (hw : width ≤ budget.length) (hi : index ≤ budget.length) :
    remap (budget,((width,base),(refs,index))) = CircuitRelocate.remap width base refs index := by
  have hflag : TM2BoundedWitnessGuard.guard (TM2BoundedUnary.expand (budget,width),index) = decide (index < width) := by
    rw [TM2TapePairs.guard_eq_decide,TM2BoundedUnary.expand_correct,List.length_replicate,Nat.min_eq_left hw]
  simp only [remap,hflag,decide_eq_true_eq,CircuitRelocate.remap,
    TM2BoundedSubtract.subtract_exact budget index width hi hw]

namespace Fixtures
example : remap ([true,true,true],((2,9),([7,8],1))) = 8 := rfl
example : remap ([true,true,true],((2,9),([7,8],3))) = 10 := rfl
example : remap ([],((4,9),([7,8],100))) = 9 := rfl
end Fixtures
end Shared.ComplexityBridge.TM2BoundedRemap
