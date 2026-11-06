import Shared.Beeping.NPcoNP.Source284HardwireReference
import Shared.Beeping.NPcoNP.Source284Truncation

/-! The hardwired loader preserves its certificate exactly.  Nevertheless,
the reference frame searches certificates using the longer loader-inclusive
clock. Every original T-step attempt depends only on its low T certificate
bits, so that larger finite search is extensionally equivalent to the T-bit
search. We do not claim oversized certificates reject, nor that a longer
execution preserves a timed-out rejection. -/

namespace Shared.Beeping.NPcoNP.Source284HardwireWitness

open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable
open Shared.Beeping.NPcoNP.Source284HardwireReference
open Shared.Beeping.NPcoNP.Source284TableFrame
open Shared.Beeping.NPcoNP.Source284TableClock
open Shared.Beeping.NPcoNP.Source284HardnessFramePoly
open Shared.Beeping.NPcoNP.Source284Comparison

/-- Any finite relative table can observe at most its original clock's
number of certificate bits, including when the input has trailing zeros. -/
theorem table_accepts_truncate (bits : List Bool) (original : Nat → Bool → Row)
    (n : Nat) (hn : 0 < n) (hclosed : Closed n original)
    (certificate clock : Nat) :
    (run original ⟨certificate,value bits,some 0⟩ clock).state.isNone =
      (run original ⟨certificate % 2^clock,value bits,some 0⟩ clock).state.isNone := by
  have h := Source284Relative.accepts_truncate (encode n original 0)
    (value bits) certificate clock
  rw [bounded_acceptance n original 0 hn hclosed (value bits) certificate clock,
    bounded_acceptance n original 0 hn hclosed (value bits) (certificate % 2^clock) clock] at h
  exact h

/-- The actual source-reference witness search can be reduced to the
original clock's bit bound, without asking the machine to reject larger
natural certificates. -/
theorem reference_hardwired_original_witness_bound
    (bits : List Bool) (original : Nat → Bool → Row) (n : Nat)
    (hn : 0 < n) (hclosed : Closed n original) (clock : Nat)
    (hclock : (programBits (offset bits+n) (table bits original)).length + 1 ≤
      offset bits+clock) :
    reference (value (produceSafe (programBits (offset bits+n) (table bits original),
      padFor (programBits (offset bits+n) (table bits original)) (offset bits+clock)))) = true ↔
      ∃ certificate, certificate < 2 ^ clock ∧
        (run original ⟨certificate,value bits,some 0⟩ clock).state.isNone = true := by
  rw [reference_hardwired_table bits original n hn hclosed clock hclock]
  constructor
  · rintro ⟨certificate, _, haccept⟩
    refine ⟨certificate % 2^clock, Nat.mod_lt _ (by positivity), ?_⟩
    rw [← table_accepts_truncate bits original n hn hclosed certificate clock]
    exact haccept
  · rintro ⟨certificate, hsmall, haccept⟩
    refine ⟨certificate, ?_, haccept⟩
    exact lt_of_lt_of_le hsmall
      (Nat.pow_le_pow_right (by decide) (by omega : clock ≤ offset bits+clock))

end Shared.Beeping.NPcoNP.Source284HardwireWitness
