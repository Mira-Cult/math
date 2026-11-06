import Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

/-! Read the first encoded unary block without assumptions about the rest
of the tape. -/
namespace Shared.Beeping.NPcoNP.NativeHalfBankFirst

open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- The first encoded value has exactly `v+1` ones followed by a zero. -/
theorem first_block_cells (t : Int → Bool) (a : Int) (v : Nat) (xs : List Nat)
    (ht : Holds t a (encode (v::xs))) :
    (∀ i : Nat, i≤v → t (a+(i : Int))=true) ∧
      t (a+((v+1 : Nat) : Int))=false := by
  have hword : encode (v::xs) = List.replicate (v+1) true ++ (false :: encode xs) := by
    simp [encode,block,List.append_assoc]
  rw [hword] at ht
  constructor
  · intro i hi
    have hi' : i<(List.replicate (v+1) true ++ (false :: encode xs)).length := by simp; omega
    have hh := holds_get t a _ ht i hi'
    have hir : i<(List.replicate (v+1) true).length := by simp; omega
    have he : (List.replicate (v+1) true ++ (false :: encode xs))[i]'hi'=true := by
      rw [List.getElem_append_left hir]
      simp
    rw [he] at hh
    exact hh
  · let i := v+1
    have hi : i<(List.replicate (v+1) true ++ (false :: encode xs)).length := by dsimp [i]; simp
    have hh := holds_get t a _ ht i hi
    have he : (List.replicate (v+1) true ++ (false :: encode xs))[i]'hi=false := by
      dsimp [i]
      simp
    rw [he] at hh
    exact hh

/-- A finite prefix can be dropped while retaining the following tape word. -/
theorem holds_append_tail (t : Int → Bool) (a : Int) (xs ys : List Bool)
    (ht : Holds t a (xs++ys)) : Holds t (a+((xs.length : Nat) : Int)) ys := by
  induction xs generalizing a with
  | nil => simpa using ht
  | cons x xs ih =>
    simp only [List.cons_append,Holds] at ht
    have hh := ih (a+1) ht.2
    simpa [Int.add_assoc,Int.add_comm,Int.add_left_comm] using hh

/-- The values after the first block begin immediately after its delimiter. -/
theorem first_block_tail (t : Int → Bool) (a : Int) (v : Nat) (xs : List Nat)
    (ht : Holds t a (encode (v::xs))) :
    Holds t (a+((v+2 : Nat) : Int)) (encode xs) := by
  have ht' : Holds t a (block v ++ encode xs) := by simpa [encode] using ht
  have h := holds_append_tail t a (block v) (encode xs) ht'
  simpa [block_length] using h

end Shared.Beeping.NPcoNP.NativeHalfBankFirst

#print axioms Shared.Beeping.NPcoNP.NativeHalfBankFirst.first_block_cells
