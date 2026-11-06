import Shared.ComplexityBridge.TM2RowGates

set_option backward.isDefEq.respectTransparency false

/-! Construct the entire transition-row block for any fixed finite table.
The wire offsets are runtime values, and every repeated row is charged. -/
namespace Shared.ComplexityBridge.TM2FixedRows
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CircuitCNF

abbrev Params := (Nat × Nat) × ((Nat × Nat) × Nat)

/-- Addition of an arbitrary fixed natural is polynomial in the binary input. -/
theorem addFixed_isPolyTime (n : Nat) : ComplexityTheory.IsPolyTime (fun x : Nat => x+n) := by
  induction n with
  | zero =>
    change ComplexityTheory.IsPolyTime (id : Nat → Nat)
    exact ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  | succ n ih =>
    have h := TM2Compose.isPolyTime_comp (fun x : Nat => x+n) Nat.succ ih CNFBinaryIncrement.successor_isPolyTime
    change ComplexityTheory.IsPolyTime (fun x : Nat => Nat.succ (x+n))
    exact h

def buildArgs (row : Bool × Bool) (p : Params) : TM2RowGates.Input :=
  (p.1,(p.2.1,(p.2.2,row)))

theorem buildArgs_isPolyTime (row : Bool × Bool) : ComplexityTheory.IsPolyTime (buildArgs row) := by
  let first : Params → Nat × Nat := fun p => p.1
  let second : Params → (Nat × Nat) × Nat := fun p => p.2
  let wires : Params → Nat × Nat := fun p => p.2.1
  let acc : Params → Nat := fun p => p.2.2
  let row0 : Params → Bool := fun _ => row.1
  let row1 : Params → Bool := fun _ => row.2
  let r : Params → Bool × Bool := fun p => (row0 p,row1 p)
  let tail : Params → Nat × (Bool × Bool) := fun p => (acc p,r p)
  let rhs : Params → (Nat × Nat) × (Nat × (Bool × Bool)) := fun p => (wires p,tail p)
  have hf : ComplexityTheory.IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hs : ComplexityTheory.IsPolyTime second := TM2GuardAllStep.second_isPolyTime
  have hw : ComplexityTheory.IsPolyTime wires := TM2Compose.isPolyTime_comp second
    (fun p : (Nat × Nat) × Nat => p.1) hs TM2PairFirst.first_isPolyTime
  have ha : ComplexityTheory.IsPolyTime acc := TM2Compose.isPolyTime_comp second
    (fun p : (Nat × Nat) × Nat => p.2) hs TM2GuardAllStep.second_isPolyTime
  have h0 : ComplexityTheory.IsPolyTime row0 := TM2Constant.isPolyTime row.1
  have h1 : ComplexityTheory.IsPolyTime row1 := TM2Constant.isPolyTime row.2
  have hr : ComplexityTheory.IsPolyTime r := TM2GuardAllStep.pair_isPolyTime row0 row1 h0 h1
  have ht : ComplexityTheory.IsPolyTime tail := TM2GuardAllStep.pair_isPolyTime acc r ha hr
  have hh : ComplexityTheory.IsPolyTime rhs := TM2GuardAllStep.pair_isPolyTime wires tail hw ht
  have h := TM2GuardAllStep.pair_isPolyTime first rhs hf hh
  change ComplexityTheory.IsPolyTime (buildArgs row) at h
  exact h

def advance (p : Params) : Params :=
  ((p.1.1+4,p.1.2+1),(p.2.1,p.1.1+3))

theorem advance_isPolyTime : ComplexityTheory.IsPolyTime advance := by
  let first : Params → Nat × Nat := fun p => p.1
  let second : Params → (Nat × Nat) × Nat := fun p => p.2
  let base : Params → Nat := fun p => p.1.1
  let q : Params → Nat := fun p => p.1.2
  let wires : Params → Nat × Nat := fun p => p.2.1
  let b4 : Params → Nat := fun p => base p+4
  let q1 : Params → Nat := fun p => q p+1
  let b3 : Params → Nat := fun p => base p+3
  let left : Params → Nat × Nat := fun p => (b4 p,q1 p)
  let right : Params → (Nat × Nat) × Nat := fun p => (wires p,b3 p)
  have hf : ComplexityTheory.IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hs : ComplexityTheory.IsPolyTime second := TM2GuardAllStep.second_isPolyTime
  have hb : ComplexityTheory.IsPolyTime base := TM2Compose.isPolyTime_comp first
    (fun p : Nat × Nat => p.1) hf TM2PairFirst.first_isPolyTime
  have hq : ComplexityTheory.IsPolyTime q := TM2Compose.isPolyTime_comp first
    (fun p : Nat × Nat => p.2) hf TM2GuardAllStep.second_isPolyTime
  have hw : ComplexityTheory.IsPolyTime wires := TM2Compose.isPolyTime_comp second
    (fun p : (Nat × Nat) × Nat => p.1) hs TM2PairFirst.first_isPolyTime
  have hb4 : ComplexityTheory.IsPolyTime b4 := TM2Compose.isPolyTime_comp base (fun n => n+4) hb (addFixed_isPolyTime 4)
  have hq1 : ComplexityTheory.IsPolyTime q1 := TM2Compose.isPolyTime_comp q (fun n => n+1) hq (addFixed_isPolyTime 1)
  have hb3 : ComplexityTheory.IsPolyTime b3 := TM2Compose.isPolyTime_comp base (fun n => n+3) hb (addFixed_isPolyTime 3)
  have hl : ComplexityTheory.IsPolyTime left := TM2GuardAllStep.pair_isPolyTime b4 q1 hb4 hq1
  have hr : ComplexityTheory.IsPolyTime right := TM2GuardAllStep.pair_isPolyTime wires b3 hw hb3
  have h := TM2GuardAllStep.pair_isPolyTime left right hl hr
  change ComplexityTheory.IsPolyTime advance at h
  exact h

def build (rows : List (Bool × Bool)) (p : Params) : List Gate :=
  CircuitTable.rowsGates p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2 rows

/-- For each fixed finite transition table, the complete selector block is
computed by a finite TM2 in polynomial time in all five binary wire inputs.
The polynomial and finite program may depend on the fixed table. -/
theorem build_isPolyTime (rows : List (Bool × Bool)) : ComplexityTheory.IsPolyTime (build rows) := by
  induction rows with
  | nil =>
    have h : ComplexityTheory.IsPolyTime (fun _ : Params => ([] : List Gate)) := TM2EmptyConstant.isPolyTime [] rfl
    change ComplexityTheory.IsPolyTime (build []) at h
    exact h
  | cons row rows ih =>
    let head : Params → List Gate := fun p => TM2RowGates.build (buildArgs row p)
    let tail : Params → List Gate := fun p => build rows (advance p)
    have hh : ComplexityTheory.IsPolyTime head := TM2Compose.isPolyTime_comp (buildArgs row) TM2RowGates.build
      (buildArgs_isPolyTime row) TM2RowGates.build_isPolyTime
    have ht : ComplexityTheory.IsPolyTime tail := TM2Compose.isPolyTime_comp advance (build rows) advance_isPolyTime ih
    have h := TM2RowGates.append_isPolyTime head tail hh ht
    have he : (fun p => head p ++ tail p) = build (row::rows) := by
      funext p
      rfl
    rw [he] at h
    exact h

/-- The leading negation and false accumulator are included in the exact
lookup circuit, not supplied for free. -/
theorem lookupGates_isPolyTime (rows : List (Bool × Bool)) :
    ComplexityTheory.IsPolyTime (fun n : Nat => CircuitTable.lookupGates n rows) := by
  let ident : Nat → Nat := id
  let zero : Nat → Nat := fun _ => 0
  let b1 : Nat → Nat := fun n => n+1
  let b2 : Nat → Nat := fun n => n+2
  let b3 : Nat → Nat := fun n => n+3
  let first : Nat → Nat × Nat := fun n => (b3 n,zero n)
  let wires : Nat → Nat × Nat := fun n => (ident n,b1 n)
  let second : Nat → (Nat × Nat) × Nat := fun n => (wires n,b2 n)
  let args : Nat → Params := fun n => (first n,second n)
  let neg : Nat → Gate := Gate.neg
  let falseBit : Nat → Bool := fun _ => false
  let falseGate : Nat → Gate := fun _ => Gate.constant false
  let header : Nat → List Gate := fun n => [neg n,falseGate n]
  let body : Nat → List Gate := fun n => build rows (args n)
  have hi : ComplexityTheory.IsPolyTime ident := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hz : ComplexityTheory.IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have h1 : ComplexityTheory.IsPolyTime b1 := addFixed_isPolyTime 1
  have h2 : ComplexityTheory.IsPolyTime b2 := addFixed_isPolyTime 2
  have h3 : ComplexityTheory.IsPolyTime b3 := addFixed_isPolyTime 3
  have hf : ComplexityTheory.IsPolyTime first := TM2GuardAllStep.pair_isPolyTime b3 zero h3 hz
  have hw : ComplexityTheory.IsPolyTime wires := TM2GuardAllStep.pair_isPolyTime ident b1 hi h1
  have hs : ComplexityTheory.IsPolyTime second := TM2GuardAllStep.pair_isPolyTime wires b2 hw h2
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime first second hf hs
  have hn : ComplexityTheory.IsPolyTime neg := TM2GateConstruct.neg_isPolyTime
  have hb : ComplexityTheory.IsPolyTime falseBit := TM2Constant.isPolyTime false
  have hg : ComplexityTheory.IsPolyTime falseGate := TM2Compose.isPolyTime_comp falseBit Gate.constant hb TM2BinaryListLength.constantGate_isPolyTime
  have hh : ComplexityTheory.IsPolyTime header := TM2GateCNFPieces.pairList_isPolyTime neg falseGate hn hg
  have hbody : ComplexityTheory.IsPolyTime body := TM2Compose.isPolyTime_comp args (build rows) ha (build_isPolyTime rows)
  have h := TM2RowGates.append_isPolyTime header body hh hbody
  change ComplexityTheory.IsPolyTime (fun n : Nat => CircuitTable.lookupGates n rows) at h
  exact h

namespace Fixtures
example : build [(false,true),(true,false)] ((10,2),((4,5),7)) =
  [.constant false,.conj 2 4,.disj 10 11,.disj 7 12,
   .conj 3 5,.constant false,.disj 14 15,.disj 13 16] := rfl
example : build [] ((10,2),((4,5),7)) = [] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2FixedRows
