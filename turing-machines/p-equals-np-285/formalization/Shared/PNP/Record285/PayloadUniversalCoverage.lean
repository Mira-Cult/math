import Shared.PNP.Record285.PayloadClosed

/-! Uniform coverage of polynomial-time payload deciders by the literal
source's program-and-clock enumeration. This theorem is independent of the
reference language and of P = NP. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
noncomputable section
namespace Shared.PNP.Record285.PayloadUniversalCoverage
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.CanonicalInput
open Shared.PNP.Record285.CanonicalPolynomialCoverage
open Shared.PNP.Record285.PayloadClosed
open Shared.Codes.FinitePrograms

/-- Every canonical polynomial-time Boolean predicate has one source program
and one positive clock exponent which compute it on all finite payloads,
including the empty word. The payload is encoded by its length and value. -/
theorem polynomial_payload_candidate (f : List Bool → Bool)
    (hf : ComplexityTheory.IsPolyTime f) :
    ∃ program exponent, 0 < exponent ∧ ∀ size value, value < 2^size →
      candidate program exponent size (2^size) value = f (bits size value) := by
  let reversed : List Bool → Bool := fun xs => f xs.reverse
  have hrev : ComplexityTheory.IsPolyTime reversed := by
    exact Shared.ComplexityBridge.TM2Compose.isPolyTime_comp
      (List.reverse : List Bool → List Bool) f
      (Shared.ComplexityBridge.TM2ListReverse.reverse_isPolyTime (α := Bool)) hf
  obtain ⟨p,q,hvalid,hcorrect⟩ :=
    (Shared.Codes.FiniteProgramSingleUntag.canonical_decision_iff_finite reversed).1 hrev
  have hcoverage := finite_program_encoded_polynomial_coverage
    (PayloadHandoff.reflectedProgram p) (fun size value => f (bits size value)) (budget q)
  have hbounded : ∀ size value, value < 2^size →
      bounded (PayloadHandoff.reflectedProgram p) (canonical (bits size value))
        ((budget q).eval (BitstringEncoding.bitEncode (canonical (bits size value))).length) =
          some (f (bits size value)) := by
    intro size value hv
    let payload := bits size value
    let fuel := q.eval (BitstringEncoding.bitEncode payload.reverse).length
    have hc := hcorrect payload.reverse
    have hc' : bounded p (BitstringEncoding.bitEncode payload.reverse) fuel = some (f payload) := by
      simpa [fuel,reversed] using hc
    have hr := PayloadHandoff.bounded_reflected p hvalid payload fuel
    rw [hc'] at hr
    obtain ⟨t,ht,hres⟩ := (bounded_iff_result (PayloadHandoff.reflectedProgram p)
      (canonical payload) (PayloadEncoding.duration payload+2+fuel) _).1 hr
    apply (bounded_iff_result (PayloadHandoff.reflectedProgram p) (canonical payload)
      ((budget q).eval (BitstringEncoding.bitEncode (canonical payload)).length) _).2
    exact ⟨t,le_trans ht (by simpa [fuel] using budget_bound q payload),hres⟩
  obtain ⟨program,exponent,hpos,hcandidate⟩ := hcoverage hbounded
  refine ⟨program,exponent,hpos,?_⟩
  intro size value hv
  have h := hcandidate size value hv
  cases hc : candidate program exponent size (2^size) value <;>
    cases hf : f (bits size value) <;> simp_all

/-- The same single candidate works for every bitstring, including malformed
frames: malformed inputs are rejected and valid frames return the predicate's
answer on the complete payload, including trailing zero bits. -/
theorem polynomial_framed_candidate (f : List Bool → Bool)
    (hf : ComplexityTheory.IsPolyTime f) :
    ∃ program exponent, 0 < exponent ∧ ∀ input,
      candidateLanguage program exponent input =
        match CanonicalInput.parse input with
        | none => false
        | some payload => f payload := by
  obtain ⟨program,exponent,hpos,hcandidate⟩ := polynomial_payload_candidate f hf
  refine ⟨program,exponent,hpos,?_⟩
  intro input
  cases hp : CanonicalInput.parse input with
  | none => simp [candidateLanguage,hp]
  | some payload =>
    have h := hcandidate payload.length (value payload) (value_lt_pow payload)
    have hbits : bits payload.length (value payload) = payload := by
      simpa using Shared.PNP.Record285.ReferenceSerialization.bits_value_pad payload 0
    simpa [candidateLanguage,hp,hbits] using h

end Shared.PNP.Record285.PayloadUniversalCoverage
