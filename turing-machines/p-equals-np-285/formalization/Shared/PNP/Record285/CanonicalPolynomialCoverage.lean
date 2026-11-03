import Shared.PNP.Record285.FiniteProgramAdapter
import Shared.ComplexityBridge.Encodings

/-! The pinned canonical Boolean-list encoding has three bits per raw frame
bit. This adapts its polynomial bounds; it does not construct the required
finite-program raw-input loader. -/
namespace Shared.PNP.Record285.CanonicalPolynomialCoverage
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.CanonicalInput
open Shared.PNP.Record285.FiniteProgramAdapter
open Shared.Codes.FinitePrograms

/-- Exact canonical-library input length, including the zero-length payload. -/
theorem encoded_frame_length (payload : List Bool) :
    (BitstringEncoding.bitEncode (canonical payload)).length = 3*(2*payload.length+1) := by
  rw [Shared.ComplexityBridge.bitstring_list_encoded_length, canonical_length]

/-- Uniform finite-program coverage when the supplied polynomial is measured
in the pinned canonical encoding length rather than the raw frame length. -/
theorem finite_program_encoded_polynomial_coverage
    (p : Program) (answer : Nat → Nat → Bool) (bound : Polynomial Nat)
    (hcorrect : ∀ size payload, payload < 2^size →
      bounded p (canonical (bits size payload))
        (bound.eval (BitstringEncoding.bitEncode (canonical (bits size payload))).length) =
          some (answer size payload)) :
    ∃ program exponent, 0 < exponent ∧ ∀ size payload, payload < 2^size →
      (candidate program exponent size (2^size) payload = true ↔ answer size payload = true) := by
  apply finite_program_canonical_coverage p answer (bound.comp (Polynomial.C 3 * Polynomial.X))
  intro size payload hp
  have h := hcorrect size payload hp
  rw [encoded_frame_length, bits_length] at h
  simpa only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using h

/-- A finite program satisfying the exact reference predicate under a canonical
encoded-length polynomial bound makes the abstract source eventually silent. -/
theorem source_silent_of_encoded_polynomial_program (p : Program) (bound : Polynomial Nat)
    (hcorrect : ∀ size payload, payload < 2^size →
      bounded p (canonical (bits size payload))
        (bound.eval (BitstringEncoding.bitEncode (canonical (bits size payload))).length) =
          some (reference size (2^size) payload)) :
    controller.EventuallySilent := by
  obtain ⟨program,exponent,hpos,hcorrect'⟩ :=
    finite_program_encoded_polynomial_coverage p
      (fun size payload => reference size (2^size) payload) bound hcorrect
  apply eventuallySilent_iff_goodCandidate.mpr
  refine ⟨program,exponent,hpos,?_⟩
  intro size payload hp
  have h := hcorrect' size payload hp
  unfold mismatch
  cases hc : candidate program exponent size (2^size) payload <;>
    cases hr : reference size (2^size) payload <;> simp_all

end Shared.PNP.Record285.CanonicalPolynomialCoverage
