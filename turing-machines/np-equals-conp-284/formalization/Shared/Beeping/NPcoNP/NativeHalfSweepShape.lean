import Shared.Beeping.NPcoNP.NativeHalfSweep
import Shared.Beeping.NPcoNP.NativeHalfBankBridge
import Shared.Beeping.NPcoNP.UnarySuffixShift

/-! Every finite encoded unary bank, read backwards, has the shape accepted
by the literal backward sweep. The specified two-sided before tape has the
needed descending bit values through the two-zero gap. No full shifted-tape
postcondition is claimed in this module. -/
namespace Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.UnarySuffixShift

theorem prefix_reverse_block (x : Nat) : Prefix (UnaryBank.block x).reverse := by
  change Prefix ((List.replicate (x+1) true ++ [false]).reverse)
  rw [List.reverse_append, List.reverse_replicate, List.replicate_succ]
  exact Prefix.zeroOne (prefix_ones x)

theorem prefix_reverse_bank (xs : List Nat) : Prefix (UnaryBank.encode xs).reverse := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    simp only [UnaryBank.encode, List.reverse_append]
    exact prefix_append ih (prefix_reverse_block x)

theorem shape_of_prefix (xs : List Bool) (h : Prefix xs) : ∃ s : Shape, bits s = xs := by
  induction h with
  | nil => exact ⟨.stop, rfl⟩
  | one h ih => obtain ⟨s, hs⟩ := ih; exact ⟨.one s, by simp [bits, hs]⟩
  | zeroOne h ih => obtain ⟨s, hs⟩ := ih; exact ⟨.zeroOne s, by simp [bits, hs]⟩

theorem shape_reverse_bank (xs : List Nat) : ∃ s : Shape, bits s = (UnaryBank.encode xs).reverse :=
  shape_of_prefix _ (prefix_reverse_bank xs)
end Shared.Beeping.NPcoNP.NativeHalfSweep
namespace Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.UnarySuffixShift

theorem down_of_get (tape : Int → Bool) (h : Int) (xs : List Bool)
    (ht : ∀ i, (hi : i < xs.length) → tape (h - (i : Int)) = xs[i]) : downHolds tape h xs := by
  induction xs generalizing h with
  | nil => trivial
  | cons x xs ih =>
    constructor
    · have hh := ht 0 (by simp)
      change tape (h - 0) = x at hh
      simpa using hh
    · apply ih
      intro i hi
      have hh := ht (i+1) (by simp; omega)
      simpa [Int.sub_sub, Int.add_comm] using hh

theorem down_before_reverse (base : Int → Bool) (gap : Int) (suffix : List Bool) :
    downHolds (before base gap suffix) (gap+1+suffix.length) (suffix.reverse ++ [false,false]) := by
  apply down_of_get
  intro i hi
  by_cases h : i < suffix.length
  · have hr : i < suffix.reverse.length := by simpa using h
    rw [List.getElem_append_left hr, List.getElem_reverse]
    have hj : suffix.length - 1 - i < suffix.length := by omega
    have he : gap+1+(suffix.length : Int) - (i : Int) = gap+2+((suffix.length-1-i : Nat) : Int) := by omega
    rw [he, before_suffix_bit]
    simp [bitAt, List.getElem?_eq_getElem hj]
  · have hib : i < suffix.length + 2 := by simpa using hi
    have he : i = suffix.length ∨ i = suffix.length+1 := by omega
    rcases he with h0 | h1
    · subst i
      simp [before]
    · subst i
      have heq : gap+1+(suffix.length : Int) - ((suffix.length+1 : Nat) : Int) = gap := by omega
      rw [heq]
      simp [before]
end Shared.Beeping.NPcoNP.NativeHalfSweep
