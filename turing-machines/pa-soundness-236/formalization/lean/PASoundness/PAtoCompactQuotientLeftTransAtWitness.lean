import PASoundness.PAtoCompactCompositionSharedTransitivity
import PASoundness.PAtoCompactCandidateSymmetryObject

/-! Capture-safe K specialization of the existing candidate-guarded
transitivity proof at the quotient-order witness label 7. The literal
candidate and both E premises remain object-level antecedents; this does not
by itself prove order substitutivity or any further quotient/PA property. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotientLeftTransAtWitness
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateSymmetryObject
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactConditionalTransitivityWitnessInterface
open PASoundness.PAtoCompactCompositionSharedTransitivity

/-- Exact named body of the already proved candidate-guarded transitivity. -/
def transBody : Formula := .imp (namedSymmetryCandidate 0)
  (.imp equivalentFormula (.imp secondEquivalent targetEquivalent))

theorem trans_body_code : transBody.encode =
    imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp equivalentFormula.encode (imp secondEquivalent.encode targetEquivalent.encode)) := by
  rfl

/-- The target name 8 and replacement name 7 avoid every binder in the exact
body; replacement leaves the candidate and first E hypothesis untouched. -/
theorem witness_substitution :
    replace 8 7 transBody = .imp (namedSymmetryCandidate 0)
      (.imp equivalentFormula (.imp (replace 0 1 (replace 1 7 equivalentFormula))
        (replace 1 7 equivalentFormula))) := by decide

/-- The actual K transitivity theorem specialized to the quotient-order
representative name 7, retaining its candidate-source guard. -/
def trans_at_witness : KDerivation
    (imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp equivalentFormula.encode
        (imp (replace 0 1 (replace 1 7 equivalentFormula)).encode
          (replace 1 7 equivalentFormula).encode))) := by
  have hall : KDerivation (allCode 8 transBody.encode) := by
    rw [trans_body_code]
    exact .generalize 8 shared_candidate_transitivity
  have hi := universalInstance 8 7 transBody (by decide) (by decide) (by decide)
  rw [witness_substitution] at hi
  exact .mp hall hi

theorem trans_at_witness_certificate : theoremCode (certificate trans_at_witness) =
    imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp equivalentFormula.encode
        (imp (replace 0 1 (replace 1 7 equivalentFormula)).encode
          (replace 1 7 equivalentFormula).encode)) :=
  certificate_correct trans_at_witness

end PASoundness.PAtoCompactQuotientLeftTransAtWitness

#print axioms PASoundness.PAtoCompactQuotientLeftTransAtWitness.trans_at_witness
#print axioms PASoundness.PAtoCompactQuotientLeftTransAtWitness.trans_at_witness_certificate
