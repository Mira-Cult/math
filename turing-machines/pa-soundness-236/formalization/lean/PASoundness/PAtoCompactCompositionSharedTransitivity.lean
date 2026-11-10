import PASoundness.PAtoCompactCompositionCandidateAlpha
import PASoundness.PAtoCompactPartialCompositionSelectionClosed

/-! Align the proved candidate-restricted K transitivity theorem to the exact
witness-binder convention of the existing symmetry theorem. The candidate
condition remains an explicit object-level hypothesis; no PA proof transport,
arithmetic operations or further quotient laws follow. -/
namespace PASoundness.PAtoCompactCompositionSharedTransitivity
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCompositionCandidateAlpha
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityWitnessInterface
open PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactPartialCompositionSelectionClosed

/-- Transitivity of the exact isomorphism proposal under the existing literal
symmetry candidate. Both E premises and the target are unchanged. -/
def shared_candidate_transitivity : KDerivation
    (imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp equivalentFormula.encode (imp secondEquivalent.encode targetEquivalent.encode))) := by
  have hc : KDerivation
      (imp (candidateCode 0 37 32 33 34 30 35 13 36)
        (imp equivalentFormula.encode (imp secondEquivalent.encode targetEquivalent.encode))) := by
    simpa only [named_candidate_code] using candidate_transitivity
  exact compose symmetry_to_composition hc

theorem shared_candidate_transitivity_certificate :
    theoremCode (certificate shared_candidate_transitivity) =
      imp (candidateCode 0 37 32 33 34 30 35 10 36)
        (imp equivalentFormula.encode (imp secondEquivalent.encode targetEquivalent.encode)) :=
  certificate_correct shared_candidate_transitivity

end PASoundness.PAtoCompactCompositionSharedTransitivity

#print axioms PASoundness.PAtoCompactCompositionSharedTransitivity.shared_candidate_transitivity
#print axioms PASoundness.PAtoCompactCompositionSharedTransitivity.shared_candidate_transitivity_certificate
