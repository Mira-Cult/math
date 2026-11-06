import Shared.Beeping.NPcoNP.Source284ComparisonBridge
import Shared.Codes.BinaryAdditionCanonical

/-! The actual reference comparison has a binary witness of bounded length.
This is the extensional witness interface only: no polynomial-time checker,
physical implementation, or complexity-class membership is asserted. -/
namespace Shared.Beeping.NPcoNP.Source284Witness

open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Codes.BitNumeralCompare (value)

/-- A raw little-endian list represents a number smaller than 2 to its
length, even when it contains redundant zero bits. -/
theorem value_lt_pow_length (bits : List Bool) : value bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [value]
  | cons b bs ih =>
    simp only [value, List.length_cons, pow_succ]
    cases b <;> simp_all <;> omega

/-- A certificate below the source's bound has a bit-list representation
whose raw length is no greater than the source clock. -/
theorem bounded_numeral (certificate clock : Nat) (h : certificate < 2 ^ clock) :
    ∃ bits : List Bool, bits.length ≤ clock ∧ value bits = certificate := by
  refine ⟨certificate.bits, ?_, Shared.Codes.BinaryAdditionCanonical.value_bits certificate⟩
  simpa [Nat.size_eq_bits_len] using (Nat.size_le.mpr h : certificate.size ≤ clock)

/-- The reference accepts exactly when one binary certificate of at most
the parsed length makes the independent bounded attempt accept. -/
theorem reference_iff_bounded_bits (i : Nat) :
    reference i = true ↔
      ∃ bits : List Bool, bits.length ≤ Source284Parser.length i ∧
        accepts (Source284Parser.description i) 0 (value bits)
          (Source284Parser.length i) = true := by
  rw [reference_exact, acceptBound_iff]
  constructor
  · rintro ⟨certificate, hc, ha⟩
    obtain ⟨bits, hb, hv⟩ := bounded_numeral certificate _ hc
    exact ⟨bits, hb, by simpa [hv] using ha⟩
  · rintro ⟨bits, hb, ha⟩
    refine ⟨value bits, ?_, ha⟩
    exact lt_of_lt_of_le (value_lt_pow_length bits)
      (Nat.pow_le_pow_right (by decide) hb)

end Shared.Beeping.NPcoNP.Source284Witness
