import Shared.ComplexityBridge.TM2BoundedGateRename

set_option backward.isDefEq.respectTransparency false

/-! Update all next-state wire references with an explicit unary budget. -/
namespace Shared.ComplexityBridge.TM2BoundedNextRefs
open Shared.ComplexityBridge

abbrev Context := TM2BoundedGateRename.Context
abbrev Input := Context × Nat

def step (p : Input) : Nat :=
  TM2BoundedRemap.remap (p.1.1,(p.1.2.1,(p.1.2.2,p.2)))

theorem step_isPolyTime : ComplexityTheory.IsPolyTime step := by
  let ctx : Input → Context := fun p => p.1
  let index : Input → Nat := fun p => p.2
  let budget : Input → List Bool := fun p => (ctx p).1
  let tail : Input → (Nat × Nat) × List Nat := fun p => (ctx p).2
  let dims : Input → Nat × Nat := fun p => (tail p).1
  let refs : Input → List Nat := fun p => (tail p).2
  let args : Input → TM2BoundedRemap.Input := fun p => (budget p,(dims p,(refs p,index p)))
  have hc : ComplexityTheory.IsPolyTime ctx := TM2PairFirst.first_isPolyTime
  have hi : ComplexityTheory.IsPolyTime index := TM2GuardAllStep.second_isPolyTime
  have hb : ComplexityTheory.IsPolyTime budget := TM2Compose.isPolyTime_comp ctx (fun p : Context => p.1) hc TM2PairFirst.first_isPolyTime
  have ht : ComplexityTheory.IsPolyTime tail := TM2Compose.isPolyTime_comp ctx (fun p : Context => p.2) hc TM2GuardAllStep.second_isPolyTime
  have hd : ComplexityTheory.IsPolyTime dims := TM2Compose.isPolyTime_comp tail (fun p : (Nat × Nat) × List Nat => p.1) ht TM2PairFirst.first_isPolyTime
  have hr : ComplexityTheory.IsPolyTime refs := TM2Compose.isPolyTime_comp tail (fun p : (Nat × Nat) × List Nat => p.2) ht TM2GuardAllStep.second_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime budget (fun p => (dims p,(refs p,index p))) hb
    (TM2GuardAllStep.pair_isPolyTime dims (fun p => (refs p,index p)) hd (TM2GuardAllStep.pair_isPolyTime refs index hr hi))
  have h := TM2Compose.isPolyTime_comp args TM2BoundedRemap.remap ha TM2BoundedRemap.remap_isPolyTime
  change ComplexityTheory.IsPolyTime step at h
  exact h

def next (p : Context × List Nat) : List Nat := TM2ContextMapGeneric.contextMap step p

theorem next_isPolyTime : ComplexityTheory.IsPolyTime next :=
  TM2ContextMapGeneric.contextMap_isPolyTime step step_isPolyTime

theorem next_correct (budget : List Bool) (width base : Nat) (inputs outputs : List Nat)
    (hw : width ≤ budget.length) (ho : ∀ o ∈ outputs, o ≤ budget.length) :
    next ((budget,((width,base),inputs)),outputs) = CircuitRelocate.nextRefs width base inputs outputs := by
  unfold next TM2ContextMapGeneric.contextMap CircuitRelocate.nextRefs
  apply List.map_congr_left
  intro o hm
  exact TM2BoundedRemap.remap_correct budget width base inputs o hw (ho o hm)

namespace Fixtures
example : next (([true,true,true],((2,9),[7,8])),[0,1,3]) = [7,8,10] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2BoundedNextRefs
