import Shared.Beeping.NPcoNP.Source284RecordBitCost
import Shared.Codes.BitTableValidation

/-! Binary output for the 284 source's bit-list record scanner. The cost is
the sum of the scanner's bit-cell work counter and the converter's recursive
list-inspection counter. It does not charge the cost of evaluating those
counters or prove a Turing-machine implementation. -/

namespace Shared.Beeping.NPcoNP.Source284UnaryCountBits

open Shared.Beeping.NPcoNP.Source284RecordBitCost
open Shared.Beeping.NPcoNP.Source284RecordBits
open Shared.Codes.BitNumeralCompare (value)
open Shared.Codes.BitTableValidation (increment countBits countBits_value countBits_length countBits_steps)

/-- The data-only binary incrementer; unlike `increment`, it does not
construct a natural-number instrumentation counter at runtime. -/
def incrementData : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: incrementData bs

theorem incrementData_eq (bits : List Bool) :
    incrementData bits = (increment bits).1 := by
  induction bits with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [incrementData, increment, ih]

/-- Count unary-list cells using only bit-list data. -/
def countData : List Bool → List Bool
  | [] => []
  | _ :: xs => incrementData (countData xs)

theorem countData_eq (xs : List Bool) : countData xs = (countBits xs).1 := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [countData, countBits, incrementData_eq, ih]

/-- Read a record using a binary index, and represent its unary count as a
least-significant-bit-first binary list. -/
def lookupBinary (code index : List Bool) : List Bool :=
  countData (scan code index)

/-- Sum of the scan and conversion counters. The counter is a specification;
arithmetic on the counter itself is not included in this bound. -/
def lookupCost (code index : List Bool) : Nat :=
  scanCost code index + (countBits (scan code index)).2

theorem lookupBinary_value (code index : List Bool) :
    value (lookupBinary code index) =
      Shared.Beeping.NPcoNP.Source284Relative.record (value code) (value index) := by
  rw [lookupBinary, countData_eq, countBits_value, scan_correct, ← recordBits_correct]

theorem lookupBinary_length (code index : List Bool) :
    (lookupBinary code index).length ≤ code.length := by
  rw [lookupBinary, countData_eq]
  exact le_trans (countBits_length _) (scan_length_le code index)

/-- The sum of the two specified instrumentation counters is at most this
bound. The conversion counter counts recursive list inspections, rather
than separately charging every allocation or branch. Arbitrary high zero
bits and an arbitrarily long binary index are permitted. -/
theorem lookupCost_bound (code index : List Bool) :
    lookupCost code index ≤
      (code.length + 1) * (5 * index.length + 10) +
        (code.length + 1) * (code.length + 1) := by
  have hlen := scan_length_le code index
  have hpos := Nat.add_le_add_right hlen 1
  have hmul := Nat.mul_le_mul hpos hpos
  exact Nat.add_le_add (scanCost_le code index)
    (le_trans (countBits_steps _) hmul)

end Shared.Beeping.NPcoNP.Source284UnaryCountBits
