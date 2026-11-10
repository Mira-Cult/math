import PASoundness.PAtoCompactPartialInverseCandidateProjection
import PASoundness.PAtoCompactPartialInverseInductionFixture

/-! Candidate-source-restricted inversion and symmetry for the proposed
order-isomorphism equality. The exact finite K induction instance is supplied
by the imported fixture; the candidate-source formula remains an object-level
antecedent. Reflexivity, transitivity, congruence and PA translation are not
established here. Code 1 is literal compact bottom. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateRestrictedSymmetryClosed
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoSwap
open PASoundness.PAtoCompactPartialInverseAtSource PASoundness.PAtoCompactPartialInverseBijectionSymmetry
open PASoundness.PAtoCompactPartialInverseCandidateProjection PASoundness.PAtoCompactPartialInverseInductionFixture

/-- Under the candidate-source condition, every represented bijection witness
has some graph agreeing with its inverse on the two input domains. -/
def candidate_inverse_family_closed : KDerivation
    (imp (namedCandidate 0).encode bijectionInversePremise) :=
  candidate_inverse_family fixed_induction

/-- The proposed isomorphism equality is symmetric when its first input
satisfies the exact displayed candidate-source condition. -/
def candidate_symmetry_closed : KDerivation
    (imp (namedCandidate 0).encode (imp equivalentFormula.encode reverseEquivalent.encode)) :=
  candidate_source_symmetry fixed_induction

theorem candidate_symmetry_closed_certificate : theoremCode (certificate candidate_symmetry_closed) =
    imp (namedCandidate 0).encode (imp equivalentFormula.encode reverseEquivalent.encode) :=
  certificate_correct candidate_symmetry_closed

end PASoundness.PAtoCompactCandidateRestrictedSymmetryClosed

#print axioms PASoundness.PAtoCompactCandidateRestrictedSymmetryClosed.candidate_inverse_family_closed
#print axioms PASoundness.PAtoCompactCandidateRestrictedSymmetryClosed.candidate_symmetry_closed
#print axioms PASoundness.PAtoCompactCandidateRestrictedSymmetryClosed.candidate_symmetry_closed_certificate
