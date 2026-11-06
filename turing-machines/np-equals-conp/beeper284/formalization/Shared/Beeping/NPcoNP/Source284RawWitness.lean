import Shared.Beeping.NPcoNP.Source284Witness
import Shared.Beeping.NPcoNP.Source284WitnessInputBound
import Shared.Beeping.NPcoNP.Source284CanonicalConditional
import Shared.ComplexityBridge.Encodings

/-! A guarded raw-list witness relation for the selected source reference.
This proves the witness-size and extensional parts of NP membership only.
The relation has an executable definition, but no polynomial running-time
bound or canonical TM2 implementation is proved in this module. -/
namespace Shared.Beeping.NPcoNP.Source284RawWitness

open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Beeping.NPcoNP.Source284Witness
open Shared.Beeping.NPcoNP.Source284WitnessInputBound
open Shared.Beeping.NPcoNP.Source284CanonicalConditional

/-- Reject certificates past the original source clock before evaluating
them. This preserves the original bound when a larger outer bound is used. -/
def checker (p : List Bool × List Bool) : Bool :=
  let i := value p.1
  if p.2.length ≤ Source284Parser.length i then
    accepts (Source284Parser.description i) 0 (value p.2) (Source284Parser.length i)
  else false

theorem checker_rejects_oversize (xs w : List Bool)
    (h : Source284Parser.length (value xs) < w.length) : checker (xs,w) = false := by
  simp [checker, Nat.not_le_of_gt h]

/-- The reference is extensionally the existential language of the guarded
checker, with a witness bounded by the raw input length. -/
theorem reference_witness (xs : List Bool) :
    referenceLanguage xs = true ↔
      ∃ w : List Bool, w.length ≤ xs.length ∧ checker (xs,w) = true := by
  change reference (value xs) = true ↔ _
  rw [reference_iff_bounded_bits]
  constructor
  · rintro ⟨w, hlen, haccept⟩
    refine ⟨w, le_trans hlen (parsed_length_le_raw_length xs), ?_⟩
    simpa [checker, hlen] using haccept
  · rintro ⟨w, _, hw⟩
    by_cases hlen : w.length ≤ Source284Parser.length (value xs)
    · exact ⟨w, hlen, by simpa [checker, hlen] using hw⟩
    · simp [checker, hlen] at hw

/-- The exact canonical pair encoding is linearly bounded on every witness
admitted by the outer raw-length cutoff. -/
theorem pair_encoded_length (xs w : List Bool) (h : w.length ≤ xs.length) :
    (BitstringEncoding.bitEncode (xs,w)).length ≤ 9 * xs.length + 1 := by
  rw [Shared.ComplexityBridge.bitstring_pair_encoded_length]
  omega

end Shared.Beeping.NPcoNP.Source284RawWitness
