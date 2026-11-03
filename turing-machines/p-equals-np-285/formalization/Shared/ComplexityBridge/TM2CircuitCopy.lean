import Shared.ComplexityBridge.TM2BoundedNextRefs

set_option backward.isDefEq.respectTransparency false

/-! One complete, polynomial-time circuit copy: construct and charge a unary
budget, relocate the gates, and update every next-state wire reference. -/
namespace Shared.ComplexityBridge.TM2CircuitCopy
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CircuitCNF

/-- Width tokens and base; input references and gates; output references. -/
abbrev Input := (List Bool × Nat) × ((List Nat × List Gate) × List Nat)

def budget (p : Input) : List Bool := p.1.1 ++ p.2.1.2.map (fun _ => true)

def context (p : Input) : TM2BoundedNextRefs.Context :=
  (budget p,((p.1.1.length,p.1.2),p.2.1.1))

def copy (p : Input) : List Gate × List Nat :=
  (TM2BoundedGateRename.relocate (context p,p.2.1.2),
   TM2BoundedNextRefs.next (context p,p.2.2))

theorem budget_length (p : Input) : (budget p).length = p.1.1.length+p.2.1.2.length := by
  simp [budget]

theorem copy_isPolyTime : ComplexityTheory.IsPolyTime copy := by
  let first : Input → List Bool × Nat := fun p => p.1
  let second : Input → (List Nat × List Gate) × List Nat := fun p => p.2
  let parts : Input → List Nat × List Gate := fun p => p.2.1
  let tokens : Input → List Bool := fun p => p.1.1
  let base : Input → Nat := fun p => p.1.2
  let refs : Input → List Nat := fun p => p.2.1.1
  let gates : Input → List Gate := fun p => p.2.1.2
  let outputs : Input → List Nat := fun p => p.2.2
  let bit : Gate → Bool := fun _ => true
  let gateTokens : Input → List Bool := fun p => (gates p).map bit
  let bud : Input → List Bool := budget
  let width : Input → Nat := fun p => (tokens p).length
  let dims : Input → Nat × Nat := fun p => (width p,base p)
  let ctx : Input → TM2BoundedNextRefs.Context := context
  let gargs : Input → TM2BoundedNextRefs.Context × List Gate := fun p => (ctx p,gates p)
  let nargs : Input → TM2BoundedNextRefs.Context × List Nat := fun p => (ctx p,outputs p)
  let newGates : Input → List Gate := fun p => TM2BoundedGateRename.relocate (gargs p)
  let newRefs : Input → List Nat := fun p => TM2BoundedNextRefs.next (nargs p)
  have hf : ComplexityTheory.IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hs : ComplexityTheory.IsPolyTime second := TM2GuardAllStep.second_isPolyTime
  have hp : ComplexityTheory.IsPolyTime parts := TM2Compose.isPolyTime_comp second
    (fun p : (List Nat × List Gate) × List Nat => p.1) hs TM2PairFirst.first_isPolyTime
  have ht : ComplexityTheory.IsPolyTime tokens := TM2Compose.isPolyTime_comp first (fun p : List Bool × Nat => p.1) hf TM2PairFirst.first_isPolyTime
  have hb : ComplexityTheory.IsPolyTime base := TM2Compose.isPolyTime_comp first (fun p : List Bool × Nat => p.2) hf TM2GuardAllStep.second_isPolyTime
  have hr : ComplexityTheory.IsPolyTime refs := TM2Compose.isPolyTime_comp parts (fun p : List Nat × List Gate => p.1) hp TM2PairFirst.first_isPolyTime
  have hg : ComplexityTheory.IsPolyTime gates := TM2Compose.isPolyTime_comp parts (fun p : List Nat × List Gate => p.2) hp TM2GuardAllStep.second_isPolyTime
  have ho : ComplexityTheory.IsPolyTime outputs := TM2Compose.isPolyTime_comp second (fun p : (List Nat × List Gate) × List Nat => p.2) hs TM2GuardAllStep.second_isPolyTime
  have hbit : ComplexityTheory.IsPolyTime bit := TM2Constant.isPolyTime true
  have hmap := TM2ContextMapGeneric.listMap_isPolyTime bit hbit
  have hgt : ComplexityTheory.IsPolyTime gateTokens := TM2Compose.isPolyTime_comp gates (fun gs : List Gate => gs.map bit) hg hmap
  have hbud : ComplexityTheory.IsPolyTime bud := TM2Compose.isPolyTime_comp (fun p => (tokens p,gateTokens p))
    (TM2ListAppend.append (α := Bool)) (TM2GuardAllStep.pair_isPolyTime tokens gateTokens ht hgt) TM2ListAppend.append_isPolyTime
  have hw : ComplexityTheory.IsPolyTime width := TM2Compose.isPolyTime_comp tokens List.length ht TM2BinaryListLength.length_isPolyTime
  have hd : ComplexityTheory.IsPolyTime dims := TM2GuardAllStep.pair_isPolyTime width base hw hb
  have hc : ComplexityTheory.IsPolyTime ctx := TM2GuardAllStep.pair_isPolyTime bud (fun p => (dims p,refs p)) hbud
    (TM2GuardAllStep.pair_isPolyTime dims refs hd hr)
  have hga : ComplexityTheory.IsPolyTime gargs := TM2GuardAllStep.pair_isPolyTime ctx gates hc hg
  have hna : ComplexityTheory.IsPolyTime nargs := TM2GuardAllStep.pair_isPolyTime ctx outputs hc ho
  have hng : ComplexityTheory.IsPolyTime newGates := TM2Compose.isPolyTime_comp gargs TM2BoundedGateRename.relocate hga TM2BoundedGateRename.relocate_isPolyTime
  have hnr : ComplexityTheory.IsPolyTime newRefs := TM2Compose.isPolyTime_comp nargs TM2BoundedNextRefs.next hna TM2BoundedNextRefs.next_isPolyTime
  have h := TM2GuardAllStep.pair_isPolyTime newGates newRefs hng hnr
  change ComplexityTheory.IsPolyTime copy at h
  exact h

/-- On a valid circuit with bounded output references, the charged worker
returns exactly the original relocated gate list and `nextRefs` list. -/
theorem copy_correct (widthTokens : List Bool) (base : Nat) (inputs : List Nat) (gates : List Gate) (outputs : List Nat)
    (hv : validGates widthTokens.length gates)
    (ho : ∀ o ∈ outputs, o < widthTokens.length+gates.length) :
    copy ((widthTokens,base),((inputs,gates),outputs)) =
      (CircuitRelocate.relocate widthTokens.length base inputs gates,
       CircuitRelocate.nextRefs widthTokens.length base inputs outputs) := by
  let p : Input := ((widthTokens,base),((inputs,gates),outputs))
  have hbudget : (budget p).length = widthTokens.length+gates.length := by simp [p,budget]
  have hw : widthTokens.length ≤ (budget p).length := by rw [hbudget]; omega
  have hout : ∀ o ∈ outputs, o ≤ (budget p).length := by
    intro o hm
    have h := ho o hm
    rw [hbudget]
    omega
  have hg := TM2BoundedGateRename.relocate_correct_valid (budget p) widthTokens.length base inputs gates hv (by rw [hbudget])
  have hr := TM2BoundedNextRefs.next_correct (budget p) widthTokens.length base inputs outputs hw hout
  change (TM2BoundedGateRename.relocate ((budget p,((widthTokens.length,base),inputs)),gates),
    TM2BoundedNextRefs.next ((budget p,((widthTokens.length,base),inputs)),outputs)) = _
  rw [hg,hr]

namespace Fixtures
example : copy (([true,true],9),(([7,8],[.neg 1,.conj 0 3]),[1,3])) =
    ([.neg 8,.conj 7 10],[8,10]) := rfl
example : copy (([],0),(([],[]),[])) = ([],[]) := rfl
end Fixtures
end Shared.ComplexityBridge.TM2CircuitCopy
