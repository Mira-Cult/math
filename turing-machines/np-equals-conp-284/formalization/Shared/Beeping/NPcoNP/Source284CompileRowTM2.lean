import Shared.Beeping.NPcoNP.Source284CompileRecords
import Shared.ComplexityBridge.CNFBinaryPairAdd
import Shared.ComplexityBridge.TM2BoundedWitnessGuard
import Shared.ComplexityBridge.TM2FixedRows
import Shared.ComplexityBridge.TM2If
import Shared.ComplexityBridge.TM2Constant

set_option backward.isDefEq.respectTransparency false

/-! Polynomial-time construction of each binary numeric source-table record.
The input row and its natural-number fields are arbitrary; no validity or
unary expansion assumption is made. -/
namespace Shared.Beeping.NPcoNP.Source284CompileRowTM2

open Shared.Beeping.NPcoNP.Source284CompileRecords
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge

private theorem constNat {α : Type} [BitstringEncoding α] (k : Nat) :
    ComplexityTheory.IsPolyTime (fun _ : α => k) := by
  have h := TM2Compose.isPolyTime_comp (fun _ : α => (0 : Nat))
    (fun x : Nat => x + k) TM2EmptyConstant.zero_isPolyTime (TM2FixedRows.addFixed_isPolyTime k)
  simpa using h

private theorem add {α : Type} [BitstringEncoding α] (f g : α → Nat)
    (hf : ComplexityTheory.IsPolyTime f) (hg : ComplexityTheory.IsPolyTime g) :
    ComplexityTheory.IsPolyTime (fun x => f x + g x) := by
  have h := TM2Compose.isPolyTime_comp (fun x => (f x, g x)) CNFBinaryPairAdd.addPair
    (TM2GuardAllStep.pair_isPolyTime f g hf hg) CNFBinaryPairAdd.addPair_isPolyTime
  simpa [CNFBinaryPairAdd.addPair] using h

private theorem twice {α : Type} [BitstringEncoding α] (f : α → Nat)
    (hf : ComplexityTheory.IsPolyTime f) : ComplexityTheory.IsPolyTime (fun x => 2 * f x) :=
  TM2Compose.isPolyTime_comp f (fun n : Nat => 2 * n) hf CNFBinaryIndex.double_isPolyTime

private theorem fourTimes {α : Type} [BitstringEncoding α] (f : α → Nat)
    (hf : ComplexityTheory.IsPolyTime f) : ComplexityTheory.IsPolyTime (fun x => 4 * f x) := by
  have h := twice (fun x => 2 * f x) (twice f hf)
  have he : (fun x => 2 * (2 * f x)) = (fun x => 4 * f x) := by
    funext x
    omega
  rw [he] at h
  exact h

private theorem bit_isPolyTime : ComplexityTheory.IsPolyTime bit := by
  have h := TM2If.if_isPolyTime (id : Bool → Bool) (fun _ => (1 : Nat)) (fun _ => 0)
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩ (constNat 1) (constNat 0)
  change ComplexityTheory.IsPolyTime (fun b : Bool => if b then 1 else 0)
  exact h

private theorem xor_isPolyTime : ComplexityTheory.IsPolyTime (fun p : Bool × Bool => xor p.1 p.2) := by
  have hn := TM2Compose.isPolyTime_comp (fun p : Bool × Bool => p.2) (fun b : Bool => !b)
    TM2GuardAllStep.second_isPolyTime TM2GateDispatch.not_isPolyTime
  have h := TM2If.if_isPolyTime (fun p : Bool × Bool => p.1) (fun p => !p.2) (fun p => p.2)
    TM2PairFirst.first_isPolyTime hn TM2GuardAllStep.second_isPolyTime
  have he : (fun p : Bool × Bool => if p.1 then !p.2 else p.2) =
      (fun p => xor p.1 p.2) := by
    funext p
    rcases p with ⟨a,b⟩
    cases a <;> cases b <;> rfl
  rw [he] at h
  exact h

private theorem eqFixed (k : Nat) : ComplexityTheory.IsPolyTime (fun n : Nat => decide (n = k)) := by
  have hp := TM2GuardAllStep.pair_isPolyTime (id : Nat → Nat) (fun _ => k)
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩ (constNat k)
  have hn := TM2Compose.isPolyTime_comp (fun n : Nat => (n,k)) TM2BoundedWitnessGuard.numericNe
    hp TM2BoundedWitnessGuard.numericNe_isPolyTime
  have h := TM2Compose.isPolyTime_comp (fun n : Nat => TM2BoundedWitnessGuard.numericNe (n,k))
    (fun b : Bool => !b) hn TM2GateDispatch.not_isPolyTime
  have he : (fun n : Nat => !TM2BoundedWitnessGuard.numericNe (n,k)) =
      (fun n => decide (n = k)) := by
    funext n
    by_cases h : n = k <;> simp [TM2BoundedWitnessGuard.numericNe, h]
  rw [he] at h
  exact h

theorem codeState_isPolyTime : ComplexityTheory.IsPolyTime (fun p : Nat × Bool => codeState p.1 p.2) := by
  let q : Nat × Bool → Nat := fun p => p.1
  let b : Nat × Bool → Nat := fun p => bit p.2
  have hq : ComplexityTheory.IsPolyTime q := TM2PairFirst.first_isPolyTime
  have hb : ComplexityTheory.IsPolyTime b := TM2Compose.isPolyTime_comp (fun p : Nat × Bool => p.2) bit
    TM2GuardAllStep.second_isPolyTime bit_isPolyTime
  have h := add (fun p => 4 * q p + 2 * b p) (fun _ => 1)
    (add (fun p => 4 * q p) (fun p => 2 * b p) (fourTimes q hq) (twice b hb)) (constNat 1)
  simpa [codeState, q, b] using h

theorem rejectState_isPolyTime : ComplexityTheory.IsPolyTime rejectState := by
  have hp := TM2GuardAllStep.pair_isPolyTime (id : Nat → Nat) (fun _ => false)
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩ (TM2Constant.isPolyTime false)
  have h := TM2Compose.isPolyTime_comp (fun n : Nat => (n,false))
    (fun p : Nat × Bool => codeState p.1 p.2) hp codeState_isPolyTime
  change ComplexityTheory.IsPolyTime (fun n : Nat => codeState n false)
  exact h

theorem pack_isPolyTime : ComplexityTheory.IsPolyTime (fun p : Bool × (Bool × Nat) => pack p.1 p.2.1 p.2.2) := by
  let rest : Bool × (Bool × Nat) → Bool × Nat := fun p => p.2
  let w : Bool × (Bool × Nat) → Nat := fun p => bit p.1
  let t : Bool × (Bool × Nat) → Nat := fun p => bit p.2.1
  let n : Bool × (Bool × Nat) → Nat := fun p => p.2.2
  have hr : ComplexityTheory.IsPolyTime rest := TM2GuardAllStep.second_isPolyTime
  have hw : ComplexityTheory.IsPolyTime w := TM2Compose.isPolyTime_comp (fun p : Bool × (Bool × Nat) => p.1) bit
    TM2PairFirst.first_isPolyTime bit_isPolyTime
  have ht : ComplexityTheory.IsPolyTime t := TM2Compose.isPolyTime_comp (fun p : Bool × (Bool × Nat) => p.2.1) bit
    (TM2Compose.isPolyTime_comp rest (fun p : Bool × Nat => p.1) hr TM2PairFirst.first_isPolyTime) bit_isPolyTime
  have hn : ComplexityTheory.IsPolyTime n := TM2Compose.isPolyTime_comp rest (fun p : Bool × Nat => p.2) hr TM2GuardAllStep.second_isPolyTime
  have h := add (fun p => w p + 2 * t p) (fun p => 4 * n p)
    (add w (fun p => 2 * t p) hw (twice t ht)) (fourTimes n hn)
  simpa [pack, w, t, n] using h

abbrev RowInput := (Nat × Bool) × Row

theorem encodedRow_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : RowInput => encodedRow p.1.1 p.1.2 p.2) := by
  let header : RowInput → Nat × Bool := fun p => p.1
  let row : RowInput → Row := fun p => p.2
  let size : RowInput → Nat := fun p => (header p).1
  let rev : RowInput → Bool := fun p => (header p).2
  let tail : RowInput → Bool × Nat × Nat := fun p => (row p).2
  let nums : RowInput → Nat × Nat := fun p => (tail p).2
  let write : RowInput → Bool := fun p => (row p).1
  let left : RowInput → Bool := fun p => !(tail p).1
  let dest : RowInput → Nat := fun p => (nums p).1
  let tag : RowInput → Nat := fun p => (nums p).2
  have hh : ComplexityTheory.IsPolyTime header := TM2PairFirst.first_isPolyTime
  have hr : ComplexityTheory.IsPolyTime row := TM2GuardAllStep.second_isPolyTime
  have hs : ComplexityTheory.IsPolyTime size := TM2Compose.isPolyTime_comp header (fun p : Nat × Bool => p.1) hh TM2PairFirst.first_isPolyTime
  have hv : ComplexityTheory.IsPolyTime rev := TM2Compose.isPolyTime_comp header (fun p : Nat × Bool => p.2) hh TM2GuardAllStep.second_isPolyTime
  have ht : ComplexityTheory.IsPolyTime tail := TM2Compose.isPolyTime_comp row (fun p : Row => p.2) hr TM2GuardAllStep.second_isPolyTime
  have hn : ComplexityTheory.IsPolyTime nums := TM2Compose.isPolyTime_comp tail (fun p : Bool × Nat × Nat => p.2) ht TM2GuardAllStep.second_isPolyTime
  have hw : ComplexityTheory.IsPolyTime write := TM2Compose.isPolyTime_comp row (fun p : Row => p.1) hr TM2PairFirst.first_isPolyTime
  have hl : ComplexityTheory.IsPolyTime left := TM2Compose.isPolyTime_comp (fun p : RowInput => (tail p).1) (fun b : Bool => !b)
    (TM2Compose.isPolyTime_comp tail (fun p : Bool × Nat × Nat => p.1) ht TM2PairFirst.first_isPolyTime) TM2GateDispatch.not_isPolyTime
  have hd : ComplexityTheory.IsPolyTime dest := TM2Compose.isPolyTime_comp nums (fun p : Nat × Nat => p.1) hn TM2PairFirst.first_isPolyTime
  have htag : ComplexityTheory.IsPolyTime tag := TM2Compose.isPolyTime_comp nums (fun p : Nat × Nat => p.2) hn TM2GuardAllStep.second_isPolyTime
  let turn : RowInput → Bool := fun p => xor (rev p) (left p)
  let cont : RowInput → Nat := fun p => codeState (dest p) (left p)
  let sink : RowInput → Nat := fun p => rejectState (size p)
  let isZero : RowInput → Bool := fun p => decide (tag p = 0)
  let isTwo : RowInput → Bool := fun p => decide (tag p = 2)
  have hturn : ComplexityTheory.IsPolyTime turn := TM2Compose.isPolyTime_comp (fun p => (rev p,left p))
    (fun p : Bool × Bool => xor p.1 p.2) (TM2GuardAllStep.pair_isPolyTime rev left hv hl) xor_isPolyTime
  have hc : ComplexityTheory.IsPolyTime cont := TM2Compose.isPolyTime_comp (fun p => (dest p,left p))
    (fun p : Nat × Bool => codeState p.1 p.2) (TM2GuardAllStep.pair_isPolyTime dest left hd hl) codeState_isPolyTime
  have hk : ComplexityTheory.IsPolyTime sink := TM2Compose.isPolyTime_comp size rejectState hs rejectState_isPolyTime
  have h0 : ComplexityTheory.IsPolyTime isZero := TM2Compose.isPolyTime_comp tag (fun n => decide (n = 0)) htag (eqFixed 0)
  have h2 : ComplexityTheory.IsPolyTime isTwo := TM2Compose.isPolyTime_comp tag (fun n => decide (n = 2)) htag (eqFixed 2)
  let terminal : RowInput → Nat := fun p => if isTwo p then 0 else sink p
  have hterminal : ComplexityTheory.IsPolyTime terminal := TM2If.if_isPolyTime isTwo (fun _ => 0) sink h2 (constNat 0) hk
  let next : RowInput → Nat := fun p => if isZero p then cont p else terminal p
  have hnext : ComplexityTheory.IsPolyTime next := TM2If.if_isPolyTime isZero cont terminal h0 hc hterminal
  have hargs := TM2GuardAllStep.pair_isPolyTime write (fun p => (turn p,next p)) hw
    (TM2GuardAllStep.pair_isPolyTime turn next hturn hnext)
  have h := TM2Compose.isPolyTime_comp (fun p => (write p,(turn p,next p)))
    (fun p : Bool × (Bool × Nat) => pack p.1 p.2.1 p.2.2) hargs pack_isPolyTime
  simpa [encodedRow, write, turn, next, terminal, isZero, isTwo, cont, sink, left, dest, tag, nums, tail, row, header, rev, size] using h

end Shared.Beeping.NPcoNP.Source284CompileRowTM2
