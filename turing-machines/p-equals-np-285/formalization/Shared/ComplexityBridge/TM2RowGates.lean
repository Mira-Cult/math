import Shared.ComplexityBridge.TM2GateConstruct
import Shared.ComplexityBridge.TM2ListMask

/-! Polynomial-time construction of the exact transition-table row gate
fragment, including runtime Boolean selection of gate variants. -/
namespace Shared.ComplexityBridge.TM2RowGates
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CircuitCNF

theorem append_isPolyTime {α : Type} [BitstringEncoding α] (F G : α → List Gate)
    (hF : ComplexityTheory.IsPolyTime F) (hG : ComplexityTheory.IsPolyTime G) :
    ComplexityTheory.IsPolyTime (fun x => F x ++ G x) := by
  have h := TM2GuardAllStep.pair_isPolyTime F G hF hG
  exact TM2Compose.isPolyTime_comp (fun x => (F x,G x)) (TM2ListAppend.append (α := Gate)) h TM2ListAppend.append_isPolyTime

/-- Select one conjunction or one false constant. Both candidate lists are
computed and masked by finite machines. -/
def choose (p : Bool × (Nat × Nat)) : List Gate :=
  TM2ListMask.mask (p.1,[Gate.conj p.2.1 p.2.2]) ++
    TM2ListMask.mask (!p.1,[Gate.constant false])

theorem choose_correct (b : Bool) (x y : Nat) :
    choose (b,(x,y)) = [if b then Gate.conj x y else Gate.constant false] := by
  cases b <;> rfl

theorem choose_isPolyTime : ComplexityTheory.IsPolyTime choose := by
  let flag : Bool × (Nat × Nat) → Bool := fun p => p.1
  let args : Bool × (Nat × Nat) → Nat × Nat := fun p => p.2
  let negFlag : Bool × (Nat × Nat) → Bool := fun p => !flag p
  let yes : Bool × (Nat × Nat) → Gate := fun p => Gate.conj p.2.1 p.2.2
  let noBit : Bool × (Nat × Nat) → Bool := fun _ => false
  let no : Bool × (Nat × Nat) → Gate := fun _ => Gate.constant false
  let yesList : Bool × (Nat × Nat) → List Gate := fun p => [yes p]
  let noList : Bool × (Nat × Nat) → List Gate := fun p => [no p]
  let yesMask : Bool × (Nat × Nat) → List Gate := fun p => TM2ListMask.mask (flag p,yesList p)
  let noMask : Bool × (Nat × Nat) → List Gate := fun p => TM2ListMask.mask (negFlag p,noList p)
  have hf : ComplexityTheory.IsPolyTime flag := TM2PairFirst.first_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.second_isPolyTime
  have hn : ComplexityTheory.IsPolyTime negFlag := TM2Compose.isPolyTime_comp flag (fun b => !b) hf TM2GateDispatch.not_isPolyTime
  have hy : ComplexityTheory.IsPolyTime yes := TM2Compose.isPolyTime_comp args
    (fun p : Nat × Nat => Gate.conj p.1 p.2) ha TM2GateConstruct.conj_isPolyTime
  have hnb : ComplexityTheory.IsPolyTime noBit := TM2Constant.isPolyTime false
  have hno : ComplexityTheory.IsPolyTime no := TM2Compose.isPolyTime_comp noBit Gate.constant hnb TM2BinaryListLength.constantGate_isPolyTime
  have hyl : ComplexityTheory.IsPolyTime yesList := TM2GateCNFPieces.singleton_isPolyTime yes hy
  have hnl : ComplexityTheory.IsPolyTime noList := TM2GateCNFPieces.singleton_isPolyTime no hno
  have hym : ComplexityTheory.IsPolyTime yesMask := TM2Compose.isPolyTime_comp (fun p => (flag p,yesList p))
    (TM2ListMask.mask (α := Gate)) (TM2GuardAllStep.pair_isPolyTime flag yesList hf hyl) TM2ListMask.mask_isPolyTime
  have hnm : ComplexityTheory.IsPolyTime noMask := TM2Compose.isPolyTime_comp (fun p => (negFlag p,noList p))
    (TM2ListMask.mask (α := Gate)) (TM2GuardAllStep.pair_isPolyTime negFlag noList hn hnl) TM2ListMask.mask_isPolyTime
  have h := append_isPolyTime yesMask noMask hym hnm
  change ComplexityTheory.IsPolyTime (fun p : Bool × (Nat × Nat) =>
    TM2ListMask.mask (p.1,[Gate.conj p.2.1 p.2.2]) ++ TM2ListMask.mask (!p.1,[Gate.constant false]))
  exact h

abbrev Input := (Nat × Nat) × ((Nat × Nat) × (Nat × (Bool × Bool)))

def build (p : Input) : List Gate :=
  CircuitTable.rowGates p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2

theorem build_isPolyTime : ComplexityTheory.IsPolyTime build := by
  let first : Input → Nat × Nat := fun p => p.1
  let second : Input → (Nat × Nat) × (Nat × (Bool × Bool)) := fun p => p.2
  let wires : Input → Nat × Nat := fun p => p.2.1
  let tail : Input → Nat × (Bool × Bool) := fun p => p.2.2
  let base : Input → Nat := fun p => p.1.1
  let q : Input → Nat := fun p => p.1.2
  let read : Input → Nat := fun p => p.2.1.1
  let negRead : Input → Nat := fun p => p.2.1.2
  let acc : Input → Nat := fun p => p.2.2.1
  let row : Input → Bool × Bool := fun p => p.2.2.2
  let row0 : Input → Bool := fun p => p.2.2.2.1
  let row1 : Input → Bool := fun p => p.2.2.2.2
  let i1 : Input → Nat := fun p => base p+1
  let i2 : Input → Nat := fun p => base p+2
  let firstChoice : Input → List Gate := fun p => choose (row0 p,(q p,negRead p))
  let secondChoice : Input → List Gate := fun p => choose (row1 p,(q p,read p))
  let g2 : Input → Gate := fun p => Gate.disj (base p) (i1 p)
  let g3 : Input → Gate := fun p => Gate.disj (acc p) (i2 p)
  let twoGates : Input → List Gate := fun p => [g2 p,g3 p]
  have hf : ComplexityTheory.IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hs : ComplexityTheory.IsPolyTime second := TM2GuardAllStep.second_isPolyTime
  have hws : ComplexityTheory.IsPolyTime wires := TM2Compose.isPolyTime_comp second (fun p : (Nat × Nat) × (Nat × (Bool × Bool)) => p.1) hs TM2PairFirst.first_isPolyTime
  have ht : ComplexityTheory.IsPolyTime tail := TM2Compose.isPolyTime_comp second (fun p : (Nat × Nat) × (Nat × (Bool × Bool)) => p.2) hs TM2GuardAllStep.second_isPolyTime
  have hb : ComplexityTheory.IsPolyTime base := TM2Compose.isPolyTime_comp first (fun p : Nat × Nat => p.1) hf TM2PairFirst.first_isPolyTime
  have hq : ComplexityTheory.IsPolyTime q := TM2Compose.isPolyTime_comp first (fun p : Nat × Nat => p.2) hf TM2GuardAllStep.second_isPolyTime
  have hr : ComplexityTheory.IsPolyTime read := TM2Compose.isPolyTime_comp wires (fun p : Nat × Nat => p.1) hws TM2PairFirst.first_isPolyTime
  have hn : ComplexityTheory.IsPolyTime negRead := TM2Compose.isPolyTime_comp wires (fun p : Nat × Nat => p.2) hws TM2GuardAllStep.second_isPolyTime
  have ha : ComplexityTheory.IsPolyTime acc := TM2Compose.isPolyTime_comp tail (fun p : Nat × (Bool × Bool) => p.1) ht TM2PairFirst.first_isPolyTime
  have hrow : ComplexityTheory.IsPolyTime row := TM2Compose.isPolyTime_comp tail (fun p : Nat × (Bool × Bool) => p.2) ht TM2GuardAllStep.second_isPolyTime
  have hrow0 : ComplexityTheory.IsPolyTime row0 := TM2Compose.isPolyTime_comp row (fun p : Bool × Bool => p.1) hrow TM2PairFirst.first_isPolyTime
  have hrow1 : ComplexityTheory.IsPolyTime row1 := TM2Compose.isPolyTime_comp row (fun p : Bool × Bool => p.2) hrow TM2GuardAllStep.second_isPolyTime
  have hi1 : ComplexityTheory.IsPolyTime i1 := TM2Compose.isPolyTime_comp base Nat.succ hb CNFBinaryIncrement.successor_isPolyTime
  have hi2 : ComplexityTheory.IsPolyTime i2 := TM2Compose.isPolyTime_comp base (fun n => n+2) hb TM2ShapeClauses.plusTwo_isPolyTime
  have hfirst : ComplexityTheory.IsPolyTime firstChoice := TM2Compose.isPolyTime_comp (fun p => (row0 p,(q p,negRead p))) choose
    (TM2GuardAllStep.pair_isPolyTime row0 (fun p => (q p,negRead p)) hrow0 (TM2GuardAllStep.pair_isPolyTime q negRead hq hn)) choose_isPolyTime
  have hsecond : ComplexityTheory.IsPolyTime secondChoice := TM2Compose.isPolyTime_comp (fun p => (row1 p,(q p,read p))) choose
    (TM2GuardAllStep.pair_isPolyTime row1 (fun p => (q p,read p)) hrow1 (TM2GuardAllStep.pair_isPolyTime q read hq hr)) choose_isPolyTime
  have hg2 : ComplexityTheory.IsPolyTime g2 := TM2Compose.isPolyTime_comp (fun p => (base p,i1 p)) (fun p : Nat × Nat => Gate.disj p.1 p.2)
    (TM2GuardAllStep.pair_isPolyTime base i1 hb hi1) TM2GateConstruct.disj_isPolyTime
  have hg3 : ComplexityTheory.IsPolyTime g3 := TM2Compose.isPolyTime_comp (fun p => (acc p,i2 p)) (fun p : Nat × Nat => Gate.disj p.1 p.2)
    (TM2GuardAllStep.pair_isPolyTime acc i2 ha hi2) TM2GateConstruct.disj_isPolyTime
  have htwo : ComplexityTheory.IsPolyTime twoGates := TM2GateCNFPieces.pairList_isPolyTime g2 g3 hg2 hg3
  have h := append_isPolyTime firstChoice (fun p => secondChoice p ++ twoGates p) hfirst
    (append_isPolyTime secondChoice twoGates hsecond htwo)
  have he : (fun p => firstChoice p ++ (secondChoice p ++ twoGates p)) = build := by
    funext p
    simp [firstChoice,secondChoice,twoGates,g2,g3,i1,i2,base,q,read,negRead,acc,row0,row1,
      build,CircuitTable.rowGates,choose_correct]
  rw [he] at h
  exact h

namespace Fixtures
example : build ((10,2),((4,5),(7,(false,true)))) =
    [.constant false,.conj 2 4,.disj 10 11,.disj 7 12] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2RowGates
