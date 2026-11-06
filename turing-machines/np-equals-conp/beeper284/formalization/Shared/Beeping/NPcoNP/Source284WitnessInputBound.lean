import Shared.Beeping.NPcoNP.Source284ParserSize
import Shared.Codes.BitNumeralCompare
import Mathlib.Data.Nat.Size

/-! Bounds on source-parser length in the actual raw bit-list length.
This is a size statement only, not a polynomial-time parser implementation. -/
namespace Shared.Beeping.NPcoNP.Source284WitnessInputBound

open Shared.Codes.BitNumeralCompare
open Shared.Beeping.NPcoNP.Source284Parser

theorem value_lt_pow (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
    simp only [List.length_cons, pow_succ, value]
    cases b <;> simp <;> omega

theorem value_size_le (xs : List Bool) : Nat.size (value xs) ≤ xs.length :=
  Nat.size_le.mpr (value_lt_pow xs)

theorem parsed_length_le_size (i : Nat) : length i ≤ Nat.size i := by
  have hp := parsed_length_log2 i
  have hs := Nat.lt_size_self i
  have hv : 3 * i + 1 < 2 ^ (Nat.size i + 2) := by
    rw [pow_add]
    norm_num
    omega
  have hl : Nat.log2 (3 * i + 1) < Nat.size i + 2 := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) (by omega : 3 * i + 1 ≠ 0)).2 hv
  omega

theorem parsed_length_le_raw_length (xs : List Bool) :
    length (value xs) ≤ xs.length := by
  have h := parsed_length_le_size (value xs)
  have hs := value_size_le xs
  omega

end Shared.Beeping.NPcoNP.Source284WitnessInputBound
