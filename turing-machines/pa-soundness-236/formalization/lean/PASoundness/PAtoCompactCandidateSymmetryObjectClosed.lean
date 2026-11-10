import PASoundness.PAtoCompactCandidateSymmetryObject
import PASoundness.PAtoCompactCandidateRestrictedSymmetryClosed

/-! Actual candidate-source symmetry at common object name 8, obtained by
specializing the independently constructed K symmetry derivation. This does
not align the distinct reflexivity candidate or prove transitivity. -/
namespace PASoundness.PAtoCompactCandidateSymmetryObjectClosed
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateSymmetryObject
open PASoundness.PAtoCompactCandidateRestrictedSymmetryClosed

/-- The exact symmetry candidate at 8 supports E(8,1)→E(1,8). -/
def symmetry_at_eight : KDerivation
    (imp (candidateCode 8 37 32 33 34 30 35 10 36)
      (imp equivalentEightOne.encode equivalentOneEight.encode)) :=
  specialize_symmetry candidate_symmetry_closed

theorem symmetry_at_eight_certificate : theoremCode (certificate symmetry_at_eight) =
    imp (candidateCode 8 37 32 33 34 30 35 10 36)
      (imp equivalentEightOne.encode equivalentOneEight.encode) :=
  certificate_correct symmetry_at_eight

end PASoundness.PAtoCompactCandidateSymmetryObjectClosed

#print axioms PASoundness.PAtoCompactCandidateSymmetryObjectClosed.symmetry_at_eight
#print axioms PASoundness.PAtoCompactCandidateSymmetryObjectClosed.symmetry_at_eight_certificate
