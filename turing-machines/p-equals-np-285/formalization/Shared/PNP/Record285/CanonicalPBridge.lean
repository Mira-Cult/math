import Shared.PNP.Record285.CanonicalPolynomialCoverage
import Shared.Codes.FiniteProgramSingleUntag

/-! Link the pinned canonical P-to-finite-table theorem to this source's
all-bitstring reference. The paid raw-frame encoding wrapper is an explicit,
not yet discharged, operational premise. -/
namespace Shared.PNP.Record285.CanonicalPBridge
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.CanonicalInput
open Shared.PNP.Record285.CanonicalPolynomialCoverage
open Shared.Codes.FinitePrograms

/-- If the exact all-bitstring reference is in canonical P, one fixed valid
finite table computes it on the library's encoded canonical frame. -/
theorem reference_P_has_encoded_program
    (hP : ComplexityTheory.IsPolyTime referenceLanguage) :
    ∃ p : Program, ∃ clock : Polynomial Nat, valid p = true ∧
      ∀ size payload, payload < 2^size →
        bounded p (BitstringEncoding.bitEncode (canonical (bits size payload)))
          (clock.eval (BitstringEncoding.bitEncode (canonical (bits size payload))).length) =
            some (reference size (2^size) payload) := by
  obtain ⟨p,clock,hvalid,hcorrect⟩ :=
    (Shared.Codes.FiniteProgramSingleUntag.canonical_decision_iff_finite referenceLanguage).1 hP
  refine ⟨p,clock,hvalid,?_⟩
  intro size payload hp
  have h := hcorrect (canonical (bits size payload))
  simpa [referenceLanguage, parse_canonical, bits_length, value_bits_of_lt size payload hp] using h

/-- A paid success-preserving wrapper for the actual raw self-delimiting
source frames. This is a finite-program execution statement, not a proved
loader. It must work uniformly for arbitrary valid finite continuations and
all valid payloads, including size zero, under one polynomial bound. It does
not assert a full-tape loader invariant or preserve timeout outcomes. -/
def FrameEncodingWrapper : Prop :=
  ∀ (p : Program) (clock : Polynomial Nat), valid p = true →
    ∃ (wrapped : Program) (budget : Polynomial Nat),
      ∀ size payload, payload < 2^size → ∀ result : Bool,
        bounded p (BitstringEncoding.bitEncode (canonical (bits size payload)))
          (clock.eval (BitstringEncoding.bitEncode (canonical (bits size payload))).length) = some result →
        bounded wrapped (canonical (bits size payload))
          (budget.eval (BitstringEncoding.bitEncode (canonical (bits size payload))).length) = some result

/-- Under the explicit wrapper premise, canonical P membership of the exact
reference entails eventual silence of the abstract source controller. This
result does not identify the literal table or establish P versus NP. -/
theorem source_silent_of_reference_P_and_wrapper
    (hP : ComplexityTheory.IsPolyTime referenceLanguage) (hwrap : FrameEncodingWrapper) :
    controller.EventuallySilent := by
  obtain ⟨p,clock,hvalid,hcorrect⟩ := reference_P_has_encoded_program hP
  obtain ⟨wrapped,budget,hwrapped⟩ := hwrap p clock hvalid
  apply source_silent_of_encoded_polynomial_program wrapped budget
  intro size payload hp
  exact hwrapped size payload hp _ (hcorrect size payload hp)

end Shared.PNP.Record285.CanonicalPBridge
