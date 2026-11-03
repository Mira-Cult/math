import Shared.PNP.Record285.PayloadHandoff
import Shared.PNP.Record285.PayloadPBridge
import Shared.PNP.Record285.ReferenceVerifier
import Shared.ComplexityBridge.TM2ListReverse

/-! Close the canonical-P-to-source direction using the verified physical
payload encoder, including reversal, finite handoff and polynomial clock. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
noncomputable section
namespace Shared.PNP.Record285.PayloadClosed
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.CanonicalInput
open Shared.PNP.Record285.CanonicalPolynomialCoverage
open Shared.PNP.Record285.PayloadPBridge
open Shared.Codes.FinitePrograms

def reversedReference (xs : List Bool) : Bool := payloadReference xs.reverse

theorem reversedReference_isPolyTime (hP : ComplexityTheory.IsPolyTime referenceLanguage) :
    ComplexityTheory.IsPolyTime reversedReference := by
  exact Shared.ComplexityBridge.TM2Compose.isPolyTime_comp
    (List.reverse : List Bool → List Bool) payloadReference
    (Shared.ComplexityBridge.TM2ListReverse.reverse_isPolyTime (α := Bool))
    (payloadReference_isPolyTime hP)

noncomputable def budget (q : Polynomial Nat) : Polynomial Nat :=
  Polynomial.C 288 * Polynomial.X * Polynomial.X + Polynomial.C 200 * Polynomial.X + Polynomial.C 30 + q

/-- The encoder's quadratic preparation and evaluator's own polynomial clock
are both paid by one polynomial in the encoded source-frame length. -/
theorem budget_bound (q : Polynomial Nat) (payload : List Bool) :
    PayloadEncoding.duration payload+2+
      q.eval (BitstringEncoding.bitEncode payload.reverse).length ≤
      (budget q).eval (BitstringEncoding.bitEncode (canonical payload)).length := by
  let m := (BitstringEncoding.bitEncode (canonical payload)).length
  have hm : m = 3*(2*payload.length+1) := encoded_frame_length payload
  have hn : payload.length ≤ m := by omega
  have hi : (BitstringEncoding.bitEncode payload.reverse).length ≤ m := by
    rw [Shared.ComplexityBridge.bitstring_list_encoded_length,List.length_reverse,hm]
    omega
  have hmono := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono q hi
  have hsetup := PayloadHandoff.handoff_bound payload
  change PayloadEncoding.duration payload+2+q.eval (BitstringEncoding.bitEncode payload.reverse).length ≤
    (budget q).eval m
  simp only [budget,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  nlinarith

/-- No raw-frame encoding premise is used: one valid finite binary table,
constructed from the canonical polynomial-time decider, handles every source
frame and is charged a uniform polynomial clock. -/
theorem source_silent_of_reference_P
    (hP : ComplexityTheory.IsPolyTime referenceLanguage) : controller.EventuallySilent := by
  obtain ⟨p,q,hvalid,hcorrect⟩ :=
    (Shared.Codes.FiniteProgramSingleUntag.canonical_decision_iff_finite reversedReference).1
      (reversedReference_isPolyTime hP)
  apply source_silent_of_encoded_polynomial_program (PayloadHandoff.reflectedProgram p) (budget q)
  intro size value hv
  let payload := bits size value
  let fuel := q.eval (BitstringEncoding.bitEncode payload.reverse).length
  have hc := hcorrect payload.reverse
  have hc' : bounded p (BitstringEncoding.bitEncode payload.reverse) fuel =
      some (reference size (2^size) value) := by
    simpa [fuel,reversedReference,payloadReference,payload,referenceLanguage,parse_canonical,
      bits_length,value_bits_of_lt size value hv] using hc
  have hr := PayloadHandoff.bounded_reflected p hvalid payload fuel
  rw [hc'] at hr
  obtain ⟨t,ht,hres⟩ := (bounded_iff_result (PayloadHandoff.reflectedProgram p)
    (canonical payload) (PayloadEncoding.duration payload+2+fuel) _).1 hr
  apply (bounded_iff_result (PayloadHandoff.reflectedProgram p) (canonical payload)
    ((budget q).eval (BitstringEncoding.bitEncode (canonical payload)).length) _).2
  exact ⟨t,le_trans ht (by simpa [fuel] using budget_bound q payload),hres⟩

/-- The literal machine is eventually silent exactly when canonical P = NP. -/
theorem literal_silent_iff_P_eq_NP :
    Shared.PNP.Record285.machine.system.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP := by
  constructor
  · exact Shared.PNP.Record285.CandidateCanonicalSimulation.literal_silent_implies_P_eq_NP
  · intro hp
    have href : ComplexityTheory.IsPolyTime referenceLanguage :=
      Shared.PNP.Record285.ReferenceVerifier.reference_P_iff_P_eq_NP.2 hp
    exact Shared.PNP.Record285.SourceControllerSimulation.source_eventuallySilent_iff_literal.1
      (source_silent_of_reference_P href)

theorem literal_finiteEvents_iff_P_eq_NP :
    Shared.PNP.Record285.machine.system.FiniteEventTimes ↔ ComplexityTheory.P = ComplexityTheory.NP :=
  Shared.PNP.Record285.machine.system.eventuallySilent_iff_finiteEventTimes.symm.trans
    literal_silent_iff_P_eq_NP

theorem literal_infinitelyMany_iff_P_ne_NP :
    Shared.PNP.Record285.machine.system.InfinitelyManyBeeps ↔ ComplexityTheory.P ≠ ComplexityTheory.NP := by
  rw [← Shared.Beeping.EventSystem.not_eventuallySilent_iff_infinitelyMany]
  exact not_congr literal_silent_iff_P_eq_NP

end Shared.PNP.Record285.PayloadClosed
