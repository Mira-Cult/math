import Shared.Beeping.NPcoNP.NativeHalfScan

/-! The literal forward scanner accepts a finite sequence of complete
`1^(x+1)` unary blocks beginning at a one, followed by its final delimiter and blank.
No claim about initialization, the backward shift, or full HALF is made. -/
namespace Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Table284

theorem prefix_append {xs ys : List Bool} (hx : Prefix xs) (hy : Prefix ys) : Prefix (xs ++ ys) := by
  induction hx with
  | nil => simpa using hy
  | one hx ih => exact .one ih
  | zeroOne hx ih => exact .zeroOne ih

theorem prefix_ones (k : Nat) : Prefix (List.replicate k true) := by
  induction k with
  | zero => exact .nil
  | succ k ih => simpa [List.replicate_succ] using (Prefix.one ih)

/-- Nonempty bank values encoded before their final delimiter. -/
def unaryBankPrefix (x : Nat) (xs : List Nat) : List Bool :=
  List.replicate (x+1) true ++ xs.flatMap (fun z => false :: List.replicate (z+1) true)

theorem prefix_unaryBank (x : Nat) (xs : List Nat) : Prefix (unaryBankPrefix x xs) := by
  apply prefix_append (prefix_ones (x+1))
  induction xs with
  | nil => exact .nil
  | cons z zs ih =>
    simp only [List.flatMap_cons]
    apply prefix_append
    · simpa [List.replicate_succ] using (Prefix.zeroOne (prefix_ones z))
    · exact ih

theorem selected_unary_scan (x : Nat) (xs : List Nat) (h : Int) (tape : Int → Bool)
    (hm : Holds tape h (unaryBankPrefix x xs ++ [false,false])) :
    silentSegment machine (cfg 32 h tape)
      (cfg 34 (h + (unaryBankPrefix x xs).length) tape)
      ((unaryBankPrefix x xs).length + 2) :=
  selected_scan _ (prefix_unaryBank x xs) h tape hm

end Shared.Beeping.NPcoNP.NativeHalfScan
