import Shared.ComplexityBridge.TM2ListMask
import Shared.ComplexityBridge.TM2GateDispatch

set_option backward.isDefEq.respectTransparency false

/-! A finite polynomial-time conditional on arbitrary canonically encoded
values. Masked singleton lists are read as a pair with an empty second field;
no decoder or unbounded runtime oracle is introduced. -/
namespace Shared.ComplexityBridge.TM2If
open Shared.ComplexityBridge

variable {α β : Type} [BitstringEncoding α] [BitstringEncoding β]

def chooseList (p : Bool × (β × β)) : List β :=
  TM2ListMask.mask (p.1,[p.2.1]) ++ TM2ListMask.mask (!p.1,[p.2.2])

def choosePair (p : Bool × (β × β)) : β × List β :=
  (if p.1 then p.2.1 else p.2.2,[])

theorem chooseList_bits (p : Bool × (β × β)) :
    BitstringEncoding.bitEncode (chooseList p) = BitstringEncoding.bitEncode (choosePair p) := by
  rcases p with ⟨b,x,y⟩
  cases b <;> rfl

theorem chooseList_isPolyTime : ComplexityTheory.IsPolyTime (chooseList (β := β)) := by
  let flag : Bool × (β × β) → Bool := fun p => p.1
  let vals : Bool × (β × β) → β × β := fun p => p.2
  let yes : Bool × (β × β) → β := fun p => p.2.1
  let no : Bool × (β × β) → β := fun p => p.2.2
  let neg : Bool × (β × β) → Bool := fun p => !flag p
  let ys : Bool × (β × β) → List β := fun p => [yes p]
  let ns : Bool × (β × β) → List β := fun p => [no p]
  let ym : Bool × (β × β) → List β := fun p => TM2ListMask.mask (flag p,ys p)
  let nm : Bool × (β × β) → List β := fun p => TM2ListMask.mask (neg p,ns p)
  have hf : ComplexityTheory.IsPolyTime flag := TM2PairFirst.first_isPolyTime
  have hv : ComplexityTheory.IsPolyTime vals := TM2GuardAllStep.second_isPolyTime
  have hy : ComplexityTheory.IsPolyTime yes := TM2Compose.isPolyTime_comp vals (fun p : β × β => p.1) hv TM2PairFirst.first_isPolyTime
  have hn : ComplexityTheory.IsPolyTime no := TM2Compose.isPolyTime_comp vals (fun p : β × β => p.2) hv TM2GuardAllStep.second_isPolyTime
  have hneg : ComplexityTheory.IsPolyTime neg := TM2Compose.isPolyTime_comp flag (fun b => !b) hf TM2GateDispatch.not_isPolyTime
  have hys : ComplexityTheory.IsPolyTime ys := TM2GateCNFPieces.singleton_isPolyTime yes hy
  have hns : ComplexityTheory.IsPolyTime ns := TM2GateCNFPieces.singleton_isPolyTime no hn
  have hym : ComplexityTheory.IsPolyTime ym := TM2Compose.isPolyTime_comp (fun p => (flag p,ys p))
    (TM2ListMask.mask (α := β)) (TM2GuardAllStep.pair_isPolyTime flag ys hf hys) TM2ListMask.mask_isPolyTime
  have hnm : ComplexityTheory.IsPolyTime nm := TM2Compose.isPolyTime_comp (fun p => (neg p,ns p))
    (TM2ListMask.mask (α := β)) (TM2GuardAllStep.pair_isPolyTime neg ns hneg hns) TM2ListMask.mask_isPolyTime
  have hargs := TM2GuardAllStep.pair_isPolyTime ym nm hym hnm
  have h := TM2Compose.isPolyTime_comp (fun p => (ym p,nm p)) (TM2ListAppend.append (α := β)) hargs TM2ListAppend.append_isPolyTime
  change ComplexityTheory.IsPolyTime (chooseList (β := β)) at h
  exact h

/-- Reuse the actual list-producing finite machine with the identical output
bitstring reinterpreted as a pair. -/
theorem choosePair_isPolyTime : ComplexityTheory.IsPolyTime (choosePair (β := β)) := by
  obtain ⟨m⟩ := chooseList_isPolyTime (β := β)
  refine ⟨{ toTM2ComputableAux := m.toTM2ComputableAux, time := m.time, outputsFun := ?_ }⟩
  intro p
  have h := m.outputsFun p
  change Turing.TM2OutputsInTime m.tm
    ((BitstringEncoding.bitEncode p).map m.inputAlphabet.symm)
    (some ((BitstringEncoding.bitEncode (choosePair p)).map m.outputAlphabet.symm))
    (m.time.eval (BitstringEncoding.bitEncode p).length)
  rw [←chooseList_bits]
  exact h

def choose (p : Bool × (β × β)) : β := if p.1 then p.2.1 else p.2.2

theorem choose_isPolyTime : ComplexityTheory.IsPolyTime (choose (β := β)) := by
  have h := TM2Compose.isPolyTime_comp (choosePair (β := β))
    (fun p : β × List β => p.1) (choosePair_isPolyTime (β := β)) TM2PairFirst.first_isPolyTime
  change ComplexityTheory.IsPolyTime (choose (β := β)) at h
  exact h

/-- Conditional closure includes the cost of both branches and the Boolean
selector, so each is required to have a finite polynomial-time machine. -/
theorem if_isPolyTime (flag : α → Bool) (yes no : α → β)
    (hf : ComplexityTheory.IsPolyTime flag) (hy : ComplexityTheory.IsPolyTime yes)
    (hn : ComplexityTheory.IsPolyTime no) :
    ComplexityTheory.IsPolyTime (fun x => if flag x then yes x else no x) := by
  have hv := TM2GuardAllStep.pair_isPolyTime yes no hy hn
  have hp := TM2GuardAllStep.pair_isPolyTime flag (fun x => (yes x,no x)) hf hv
  have h := TM2Compose.isPolyTime_comp (fun x => (flag x,(yes x,no x))) (choose (β := β)) hp choose_isPolyTime
  change ComplexityTheory.IsPolyTime (fun x => if flag x then yes x else no x) at h
  exact h

namespace Fixtures
example : choose (true,([true,false],[false])) = [true,false] := rfl
example : choose (false,([true,false],[false])) = [false] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2If
