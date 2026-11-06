import Shared.Beeping.NPcoNP.NativeHalfUnaryScan
import Shared.Beeping.NPcoNP.UnaryBank

/-! The scanner's finite prefix is exactly a nonempty unary-bank suffix with
its final separator removed. The one additional zero is the following blank.
This connects the forward scan to the finite-word representation; it does
not establish a tape initialization or the backward shift. -/
namespace Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Table284

def bankWords (xs : List Nat) : List Bool :=
  xs.flatMap (fun z => List.replicate (z+1) true ++ [false])

theorem bankWords_eq_encode (xs : List Nat) : bankWords xs = UnaryBank.encode xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (List.replicate (x+1) true ++ [false]) ++ bankWords xs =
      UnaryBank.block x ++ UnaryBank.encode xs
    rw [ih]
    rfl

theorem bank_tail_identity (xs : List Nat) :
    xs.flatMap (fun z => false :: List.replicate (z+1) true) ++ [false,false] =
      false :: (bankWords xs ++ [false]) := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.flatMap_cons, List.cons_append, bankWords, List.append_assoc] at *
    rw [ih]
    simp [List.append_assoc]

theorem bank_prefix_identity (x : Nat) (xs : List Nat) :
    unaryBankPrefix x xs ++ [false,false] = UnaryBank.encode (x::xs) ++ [false] := by
  rw [← bankWords_eq_encode]
  simp only [unaryBankPrefix, List.append_assoc, bank_tail_identity,
    bankWords, List.flatMap_cons, List.cons_append, List.nil_append]

/-- Exact literal scan of any nonempty encoded unary bank followed by blank. -/
theorem selected_encoded_scan (x : Nat) (xs : List Nat) (h : Int) (tape : Int → Bool)
    (hm : Holds tape h (UnaryBank.encode (x::xs) ++ [false])) :
    silentSegment machine (cfg 32 h tape)
      (cfg 34 (h + (unaryBankPrefix x xs).length) tape)
      ((unaryBankPrefix x xs).length + 2) := by
  apply selected_unary_scan
  simpa only [bank_prefix_identity] using hm

end Shared.Beeping.NPcoNP.NativeHalfScan
