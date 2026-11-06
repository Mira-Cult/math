import Shared.Beeping.NPcoNP.Source284CertificateGrammar
import Shared.ComplexityBridge.TM2ListLookup
import Shared.ComplexityBridge.TM2If
import Shared.ComplexityBridge.TM2FixedRows

/-! A total polynomial-time implementation of the five-mode grammar's next
state. Out-of-range modes return the same reject mode as the source table. -/
namespace Shared.Beeping.NPcoNP.Source284GrammarNextTM2

open ComplexityTheory Shared.ComplexityBridge

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

def lookup (xs : List Nat) (q : Nat) : Nat := (xs[q]?).getD 4

private theorem lookup_isPolyTime (xs : List Nat) : IsPolyTime (lookup xs) := by
  let rows : Nat → List Nat := fun _ => xs
  let index : Nat → Nat := id
  let fallback : Nat → Nat := fun _ => 4
  have hr : IsPolyTime rows := constList xs
  have hi : IsPolyTime index := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hf : IsPolyTime fallback := constNat 4
  have h := TM2Compose.isPolyTime_comp (fun q : Nat => (rows q,(index q,fallback q)))
    (TM2ListLookup.lookup (β := Nat))
    (TM2GuardAllStep.pair_isPolyTime rows (fun q => (index q,fallback q)) hr
      (TM2GuardAllStep.pair_isPolyTime index fallback hi hf)) TM2ListLookup.lookup_isPolyTime
  exact h

def next (p : Nat × Bool) : Nat :=
  if p.2 then lookup [1,2,4,4] p.1 else lookup [3,2,0,3] p.1

theorem next_isPolyTime : IsPolyTime next := by
  let mode : Nat × Bool → Nat := fun p => p.1
  let flag : Nat × Bool → Bool := fun p => p.2
  let yes : Nat × Bool → Nat := fun p => lookup [1,2,4,4] (mode p)
  let no : Nat × Bool → Nat := fun p => lookup [3,2,0,3] (mode p)
  have hm : IsPolyTime mode := TM2PairFirst.first_isPolyTime
  have hf : IsPolyTime flag := TM2GuardAllStep.second_isPolyTime
  have hy : IsPolyTime yes := TM2Compose.isPolyTime_comp mode _ hm (lookup_isPolyTime _)
  have hn : IsPolyTime no := TM2Compose.isPolyTime_comp mode _ hm (lookup_isPolyTime _)
  exact TM2If.if_isPolyTime flag yes no hf hy hn

theorem next_correct (mode : Nat) (read : Bool) :
    next (mode,read) = Source284CertificateGrammar.next mode read := by
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
        | succ mode => cases read <;> simp [next,lookup,Source284CertificateGrammar.next]

end Shared.Beeping.NPcoNP.Source284GrammarNextTM2
