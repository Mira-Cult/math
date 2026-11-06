import Shared.Beeping.NPcoNP.Bootstrap284BankShape

/-! The concrete checked bootstrap window decodes through the shared unary
bank decoder. This is a finite tape observation, not a runtime operation or
a proof that the physical control state matches the graph program counter. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284BankDecode

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284BankShape

def readCells (tape : Int → Bool) : Int → Nat → List Bool
  | _, 0 => []
  | h, n+1 => tape h :: readCells tape (h+1) n

theorem read_of_holds (tape : Int → Bool) (h : Int) (xs : List Bool)
    (hx : Holds tape h xs) : readCells tape h xs.length = xs := by
  induction xs generalizing h with
  | nil => rfl
  | cons x xs ih =>
    change tape h=x ∧ Holds tape (h+1) xs at hx
    simp only [List.length_cons, readCells, hx.1, ih (h+1) hx.2]

/-- At the checked physical boundary, reading the bank window and decoding
1,910 blocks yields precisely the shown values and preserves four tail bits. -/
theorem blank_start_decodes :
    decode 1910 (readCells (machine.system.run 2133492).tape (-3821) 3825) =
      some (List.replicate 1909 0 ++ [1], [true,true,true,true]) := by
  let vals := List.replicate 1909 0 ++ [1]
  let tail := [true,true,true,true]
  have hv : vals.length=1910 := by
    change (List.replicate 1909 0 ++ [1]).length=1910
    rw [List.length_append,List.length_replicate]
    decide
  have hl : (encode vals ++ tail).length=3825 := by
    change (encode (List.replicate 1909 0 ++ [1]) ++ [true,true,true,true]).length=3825
    rw [encode_append,encode_single,List.length_append,List.length_append,
      zeros_length,block_length]
    decide
  have hr := read_of_holds (machine.system.run 2133492).tape (-3821)
    (encode vals ++ tail) blank_start_bank
  rw [hl] at hr
  rw [hr]
  have hd := decode_encode vals tail
  rw [hv] at hd
  exact hd

end Shared.Beeping.NPcoNP.Bootstrap284BankDecode

#print axioms Shared.Beeping.NPcoNP.Bootstrap284BankDecode.blank_start_decodes
