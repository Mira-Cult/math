import Shared.Beeping.NPcoNP.Source284LinearPaddingTM2
import Shared.Beeping.NPcoNP.Source284TableRowsTM2

/-! Frame an explicitly supplied source-code bit list without identifying it
with the normalized numeral bits. The actual list length contributes to the
source clock, including any high zero padding. These extensional results do
not generate a table or establish a SAT reduction. -/
namespace Shared.Beeping.NPcoNP.Source284ExplicitFrame

open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable
open Shared.Beeping.NPcoNP.Source284HardwireReference
open Shared.Beeping.NPcoNP.Source284HardwireWitness
open Shared.Beeping.NPcoNP.Source284UnaryFrameReduction
open Shared.Beeping.NPcoNP.Source284HardnessFramePoly
open Shared.Beeping.NPcoNP.Source284LinearPaddingTM2
open Shared.Beeping.NPcoNP.Source284Comparison

/-- The reference clock counts the actual code list, the supplied unary
padding and the separator, whether or not the code has high zero bits. -/
theorem reference_explicit_table (n : Nat) (table : Nat → Bool → Row)
    (hn : 0 < n) (hclosed : Closed n table) (code paddingBits : List Bool)
    (tail : Nat) (hcode : value code = encode n table tail) :
    reference (value (produceSafe (code, paddingBits))) = true ↔
      ∃ certificate, certificate < 2 ^ time (code, paddingBits) ∧
        (run table ⟨certificate,0,some 0⟩ (time (code, paddingBits))).state.isNone = true := by
  rw [reduction_correct_iff]
  simp_rw [hcode, bounded_acceptance n table tail hn hclosed]

/-- A serialized explicit code of the guarded loader yields the original
finite comparison answer. The reference pays `code.length + 1` additional
steps, even when the code list has trailing high zero bits. Its witness range
is reduced extensionally by finite observation; oversized naturals are not
claimed to be rejected. An arbitrary numeric tail is permitted. -/
theorem reference_guarded_explicit
    (bits cutoff code : List Bool) (original : Nat → Bool → Row) (n tail : Nat)
    (hn : 0 < n) (hclosed : Closed n original)
    (hcode : value code = encode
      (offset bits + Source284TableCountdown.allocated n cutoff.length)
      (table bits (Source284TableCountdown.table n cutoff.length original)) tail) :
    reference (value (frame (code,bits,cutoff))) = true ↔
      ∃ certificate, certificate < 2^cutoff.length ∧
        (run original ⟨certificate,value bits,some 0⟩ cutoff.length).state.isNone = true := by
  have hpos : 0 < Source284TableCountdown.allocated n cutoff.length := by
    simp [Source284TableCountdown.allocated]
  have hguard : Closed (Source284TableCountdown.allocated n cutoff.length)
      (Source284TableCountdown.table n cutoff.length original) :=
    Source284TableCountdown.closed n cutoff.length original
  have hpos' : 0 < offset bits + Source284TableCountdown.allocated n cutoff.length := by omega
  have hclosed' : Closed (offset bits + Source284TableCountdown.allocated n cutoff.length)
      (table bits (Source284TableCountdown.table n cutoff.length original)) :=
    Source284HardwireTable.closed bits (Source284TableCountdown.table n cutoff.length original)
      _ hpos hguard
  have h := reference_explicit_table _ _ hpos' hclosed' code (padding (bits,cutoff)) tail hcode
  have ht : time (code,padding (bits,cutoff)) =
      offset bits + (cutoff.length + (code.length + 1)) := by
    simp [time, padding_length]
    omega
  rw [ht] at h
  change reference (value (frame (code,bits,cutoff))) = true ↔ _ at h
  rw [h]
  simp_rw [loader_isNone bits (Source284TableCountdown.table n cutoff.length original)
    _ (cutoff.length + (code.length + 1))]
  simp_rw [Source284TableCountdown.initial_acceptance_stable n cutoff.length original
    hn hclosed _ (value bits) (code.length+1)]
  constructor
  · rintro ⟨certificate, _, haccept⟩
    refine ⟨certificate % 2^cutoff.length, Nat.mod_lt _ (by positivity), ?_⟩
    rw [← table_accepts_truncate bits original n hn hclosed certificate cutoff.length]
    exact haccept
  · rintro ⟨certificate, hsmall, haccept⟩
    refine ⟨certificate, ?_, haccept⟩
    exact lt_of_lt_of_le hsmall
      (Nat.pow_le_pow_right (by decide) (by omega : cutoff.length ≤
        offset bits + (cutoff.length + (code.length+1))))

/-- The already proved clamped serializer satisfies the exact numeric premise
for the guarded closed table. This result assumes the guarded table's record
list is already supplied; it does not prove how to generate it in polynomial
time. -/
theorem reference_guarded_serialized
    (bits cutoff : List Bool) (original : Nat → Bool → Row) (n : Nat)
    (hn : 0 < n) (hclosed : Closed n original) :
    let guarded := table bits (Source284TableCountdown.table n cutoff.length original)
    let states := offset bits + Source284TableCountdown.allocated n cutoff.length
    let code := Source284TableRowsTM2.serializeRows (records states guarded)
    reference (value (frame (code,bits,cutoff))) = true ↔
      ∃ certificate, certificate < 2^cutoff.length ∧
        (run original ⟨certificate,value bits,some 0⟩ cutoff.length).state.isNone = true := by
  dsimp only
  apply reference_guarded_explicit bits cutoff _ original n 0 hn hclosed
  apply Source284TableRowsTM2.closed_table_correct
  apply Source284HardwireTable.closed
  · simp [Source284TableCountdown.allocated]
  · exact Source284TableCountdown.closed n cutoff.length original

end Shared.Beeping.NPcoNP.Source284ExplicitFrame
