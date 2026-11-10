import PASoundness.PAtoCompactCandidateSharedLaws
import PASoundness.PAtoCompactCandidateRestrictedSymmetryClosed

/-! The proved candidate-restricted symmetry derivation fills the explicit
proof-data premise in the shared-object reflexivity/symmetry theorem. The
candidate condition remains an object-level antecedent. No transitivity,
quotient congruence, or PA proof translation is asserted. -/
namespace PASoundness.PAtoCompactCandidateSharedLawsClosed
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateSharedLaws
open PASoundness.PAtoCompactCandidateSymmetryObject PASoundness.PAtoCompactCandidateReflexiveObject
open PASoundness.PAtoCompactCandidateRestrictedSymmetryClosed

/-- Under one candidate predicate at object 8, the same isomorphism relation
is reflexive there and symmetric for its pair with object 1. -/
def shared_laws_closed : KDerivation
    (imp (candidateCode 8 37 32 33 34 30 35 10 36)
      (both reflexive8.encode (imp equivalentEightOne.encode equivalentOneEight.encode))) :=
  shared_laws candidate_symmetry_closed

theorem shared_laws_closed_certificate : theoremCode (certificate shared_laws_closed) =
    imp (candidateCode 8 37 32 33 34 30 35 10 36)
      (both reflexive8.encode (imp equivalentEightOne.encode equivalentOneEight.encode)) :=
  certificate_correct shared_laws_closed

end PASoundness.PAtoCompactCandidateSharedLawsClosed

#print axioms PASoundness.PAtoCompactCandidateSharedLawsClosed.shared_laws_closed
#print axioms PASoundness.PAtoCompactCandidateSharedLawsClosed.shared_laws_closed_certificate
