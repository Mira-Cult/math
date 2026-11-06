import Shared.Beeping.NPcoNP.Source284TaggedScanner
import Shared.Beeping.NPcoNP.Source284GrammarNextTM2
import Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2

/-! A canonical polynomial-time evaluator for every row of the seven-mode
source tagged scanner. This operates on binary mode indices and a read bit;
it does not construct a witness bound or simulate a table on the beeper. -/
namespace Shared.Beeping.NPcoNP.Source284TaggedScannerNextTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows

private theorem constNat {α : Type} [BitstringEncoding α] (n : Nat) :
    IsPolyTime (fun _ : α => n) := by
  have hz : IsPolyTime (fun _ : α => (0 : Nat)) := TM2EmptyConstant.zero_isPolyTime
  have h := TM2Compose.isPolyTime_comp (fun _ : α => (0 : Nat)) (fun x : Nat => x+n)
    hz (TM2FixedRows.addFixed_isPolyTime n)
  simpa using h

private theorem constList {α : Type} [BitstringEncoding α] (xs : List Nat) :
    IsPolyTime (fun _ : α => xs) := by
  induction xs with
  | nil => exact TM2EmptyConstant.isPolyTime [] rfl
  | cons x xs ih =>
    have h := TM2Compose.isPolyTime_comp (fun _ : α => (x,xs))
      (TM2ListAppend.cons (α := Nat))
      (TM2GuardAllStep.pair_isPolyTime (fun _ : α => x) (fun _ => xs) (constNat x) ih)
      TM2ListAppend.cons_isPolyTime
    simpa [TM2ListAppend.cons] using h

def lookup (xs : List Nat) (q : Nat) : Nat := (xs[q]?).getD 6

private theorem lookup_isPolyTime (xs : List Nat) : IsPolyTime (lookup xs) := by
  let vals : Nat → List Nat := fun _ => xs
  let index : Nat → Nat := id
  let fallback : Nat → Nat := fun _ => 6
  have hv : IsPolyTime vals := constList xs
  have hi : IsPolyTime index := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hf : IsPolyTime fallback := constNat 6
  have h := TM2Compose.isPolyTime_comp (fun q : Nat => (vals q,(index q,fallback q)))
    (TM2ListLookup.lookup (β := Nat))
    (TM2GuardAllStep.pair_isPolyTime vals (fun q => (index q,fallback q)) hv
      (TM2GuardAllStep.pair_isPolyTime index fallback hi hf)) TM2ListLookup.lookup_isPolyTime
  exact h

def next (p : Nat × Bool) : Nat :=
  if p.2 then lookup [4,2,1,3,6,6] p.1 else lookup [4,3,1,3,5,1] p.1

theorem next_isPolyTime : IsPolyTime next := by
  let mode : Nat × Bool → Nat := fun p => p.1
  let flag : Nat × Bool → Bool := fun p => p.2
  let yes : Nat × Bool → Nat := fun p => lookup [4,2,1,3,6,6] (mode p)
  let no : Nat × Bool → Nat := fun p => lookup [4,3,1,3,5,1] (mode p)
  have hm : IsPolyTime mode := TM2PairFirst.first_isPolyTime
  have hf : IsPolyTime flag := TM2GuardAllStep.second_isPolyTime
  have hy : IsPolyTime yes := TM2Compose.isPolyTime_comp mode _ hm (lookup_isPolyTime _)
  have hn : IsPolyTime no := TM2Compose.isPolyTime_comp mode _ hm (lookup_isPolyTime _)
  exact TM2If.if_isPolyTime flag yes no hf hy hn

theorem next_correct (mode : Nat) (read : Bool) :
    (Source284TaggedScanner.table mode read).next = some (next (mode,read)) := by
  cases mode with
  | zero => cases read <;> rfl
  | succ mode =>
    cases mode with
    | zero => cases read <;> rfl
    | succ mode =>
      cases mode with
      | zero => cases read <;> rfl
      | succ mode =>
        cases mode with
        | zero => cases read <;> rfl
        | succ mode =>
          cases mode with
          | zero => cases read <;> rfl
          | succ mode =>
            cases mode with
            | zero => cases read <;> rfl
            | succ mode => cases read <;> simp [next,lookup,Source284TaggedScanner.table]

/-- The tagged scanner turns only in mode zero and preserves the read bit. -/
def turn (p : Nat × Bool) : Bool := !TM2BoundedWitnessGuard.numericNe (p.1,0)

theorem turn_isPolyTime : IsPolyTime turn := by
  let mode : Nat × Bool → Nat := fun p => p.1
  let zero : Nat × Bool → Nat := fun _ => 0
  have hm : IsPolyTime mode := TM2PairFirst.first_isPolyTime
  have hz : IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have hn := TM2Compose.isPolyTime_comp (fun p : Nat × Bool => (mode p,zero p))
    TM2BoundedWitnessGuard.numericNe (TM2GuardAllStep.pair_isPolyTime mode zero hm hz)
    TM2BoundedWitnessGuard.numericNe_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p : Nat × Bool => TM2BoundedWitnessGuard.numericNe (p.1,0))
    Bool.not hn TM2GateDispatch.not_isPolyTime

theorem turn_correct (mode : Nat) (read : Bool) :
    (Source284TaggedScanner.table mode read).turn = turn (mode,read) := by
  cases mode with
  | zero => cases read <;> rfl
  | succ mode =>
    cases mode with
    | zero => cases read <;> rfl
    | succ mode =>
      cases mode with
      | zero => cases read <;> rfl
      | succ mode =>
        cases mode with
        | zero => cases read <;> rfl
        | succ mode =>
          cases mode with
          | zero => cases read <;> rfl
          | succ mode =>
            cases mode with
            | zero => cases read <;> rfl
            | succ mode => cases read <;> simp [turn,TM2BoundedWitnessGuard.numericNe,Source284TaggedScanner.table]

def row (p : Nat × Bool) : EncRow := (p.2,turn p,true,next p)

theorem row_isPolyTime : IsPolyTime row := by
  have hb : IsPolyTime (fun p : Nat × Bool => p.2) := TM2GuardAllStep.second_isPolyTime
  have ht : IsPolyTime (fun _ : Nat × Bool => true) := TM2Constant.isPolyTime true
  exact Source284HardwireEncodedWorkersTM2.row_isPolyTime _ _ _ _ hb turn_isPolyTime ht next_isPolyTime

theorem row_correct (mode : Nat) (read : Bool) :
    decodeRow (row (mode,read)) = Source284TaggedScanner.table mode read := by
  cases mode with
  | zero => cases read <;> rfl
  | succ mode =>
    cases mode with
    | zero => cases read <;> rfl
    | succ mode =>
      cases mode with
      | zero => cases read <;> rfl
      | succ mode =>
        cases mode with
        | zero => cases read <;> rfl
        | succ mode =>
          cases mode with
          | zero => cases read <;> rfl
          | succ mode =>
            cases mode with
            | zero => cases read <;> rfl
            | succ mode => cases read <;>
              simp [decodeRow,row,turn,next,lookup,TM2BoundedWitnessGuard.numericNe,Source284TaggedScanner.table]

end Shared.Beeping.NPcoNP.Source284TaggedScannerNextTM2
