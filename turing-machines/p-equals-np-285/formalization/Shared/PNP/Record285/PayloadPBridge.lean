import Shared.PNP.Record285.CanonicalPBridge
import Shared.PNP.Record285.ReferenceSerialization

/-! Compute the source reference from the payload alone. The polynomial
transformation to the original frame is performed in the canonical
complexity model, before finite-table compilation. -/
namespace Shared.PNP.Record285.PayloadPBridge
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.CanonicalInput
open Shared.PNP.Record285.CanonicalPolynomialCoverage
open Shared.Codes.FinitePrograms

def payloadReference (payload : List Bool) : Bool := referenceLanguage (canonical payload)

/-- The original all-bitstring reference in canonical P gives a canonical
polynomial-time payload predicate using the already verified frame constructor. -/
theorem payloadReference_isPolyTime
    (hP : ComplexityTheory.IsPolyTime referenceLanguage) :
    ComplexityTheory.IsPolyTime payloadReference := by
  exact Shared.ComplexityBridge.TM2Compose.isPolyTime_comp canonical referenceLanguage
    Shared.PNP.Record285.ReferenceSerialization.canonical_isPolyTime hP

/-- One fixed binary table decides the original source predicate when fed the
canonical library encoding of the payload alone. -/
theorem reference_P_has_payload_program
    (hP : ComplexityTheory.IsPolyTime referenceLanguage) :
    ∃ p : Program, ∃ clock : Polynomial Nat, valid p = true ∧
      ∀ size payload, payload < 2^size →
        bounded p (BitstringEncoding.bitEncode (bits size payload))
          (clock.eval (BitstringEncoding.bitEncode (bits size payload)).length) =
            some (reference size (2^size) payload) := by
  obtain ⟨p,clock,hvalid,hcorrect⟩ :=
    (Shared.Codes.FiniteProgramSingleUntag.canonical_decision_iff_finite payloadReference).1
      (payloadReference_isPolyTime hP)
  refine ⟨p,clock,hvalid,?_⟩
  intro size payload hp
  have h := hcorrect (bits size payload)
  simpa [payloadReference,referenceLanguage,parse_canonical,bits_length,
    value_bits_of_lt size payload hp] using h

end Shared.PNP.Record285.PayloadPBridge
