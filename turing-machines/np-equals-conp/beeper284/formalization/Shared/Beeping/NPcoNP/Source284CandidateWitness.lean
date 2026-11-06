import Shared.Beeping.NPcoNP.Source284Witness
import Shared.Beeping.NPcoNP.Source284WitnessInputBound
import Shared.Beeping.NPcoNP.Source284CanonicalConditional

/-! The 284 source candidate's certificate search as a raw-bit witness
relation.  This is an extensional characterization and a witness-length
bound, not a canonical polynomial-time checker or an NP membership proof.
In particular the candidate receives the whole input numeral, including the
bits ignored by the source's prefix parser. -/

namespace Shared.Beeping.NPcoNP.Source284CandidateWitness

open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Beeping.NPcoNP.Source284Witness
open Shared.Beeping.NPcoNP.Source284CanonicalConditional
open Shared.Codes.BitNumeralCompare (value)

/-- The exact source candidate is an existential search over binary
certificates of length at most its own coupled clock. -/
theorem candidate_iff_bounded_bits (j i : Nat) :
    candidate j i = true ↔
      ∃ w : List Bool, w.length ≤ clock j i ∧
        accepts j i (value w) (clock j i) = true := by
  rw [candidate, acceptBound_iff]
  constructor
  · rintro ⟨certificate, hc, ha⟩
    obtain ⟨w, hw, hv⟩ := bounded_numeral certificate (clock j i) hc
    exact ⟨w, hw, by simpa [hv] using ha⟩
  · rintro ⟨w, hw, ha⟩
    refine ⟨value w, ?_, ha⟩
    exact lt_of_lt_of_le (value_lt_pow_length w)
      (Nat.pow_le_pow_right (by decide) hw)

/-- The source's parsed length is bounded by the full raw bitstring length;
the exponent is the same fixed candidate index on both sides. -/
theorem clock_le_raw_power (j : Nat) (xs : List Bool) :
    clock j (value xs) ≤ (xs.length + 1) ^ j := by
  unfold clock
  apply Nat.pow_le_pow_left
  exact Nat.add_le_add_right
    (Shared.Beeping.NPcoNP.Source284WitnessInputBound.parsed_length_le_raw_length xs) 1

/-- A polynomially bounded raw witness still has to pass the source's
original cutoff guard.  Enlarging the outer bound does not admit a new
certificate. -/
theorem candidateLanguage_iff_guarded_witness (j : Nat) (xs : List Bool) :
    candidateLanguage j xs = true ↔
      ∃ w : List Bool, w.length ≤ (xs.length + 1) ^ j ∧
        (if w.length ≤ clock j (value xs) then
          accepts j (value xs) (value w) (clock j (value xs)) else false) = true := by
  rw [candidateLanguage, candidate_iff_bounded_bits]
  constructor
  · rintro ⟨w, hw, ha⟩
    exact ⟨w, le_trans hw (clock_le_raw_power j xs), by simp [hw, ha]⟩
  · rintro ⟨w, _, ha⟩
    split_ifs at ha with hw
    · exact ⟨w, hw, ha⟩

end Shared.Beeping.NPcoNP.Source284CandidateWitness
