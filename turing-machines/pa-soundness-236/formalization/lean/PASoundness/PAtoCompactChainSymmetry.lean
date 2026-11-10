import PASoundness.PAtoCompactCandidateRestrictedSymmetryClosed
import PASoundness.PAtoCompactCandidateSymmetryObject

/-! A capture-safe fixed-name instance of the proved candidate-source
symmetry theorem. The candidate remains an explicit K antecedent; no
unrestricted symmetry or PA proof translation is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactChainSymmetry
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateSymmetryObject
open PASoundness.PAtoCompactCandidateRestrictedSymmetryClosed PASoundness.PAtoCompactOrderIsomorphism

/-- E at input names 1,8, with endpoint binders unchanged. -/
def E18 : Formula := replace 0 1 (replace 1 8 equivalentFormula)
/-- E at input names 8,1. -/
def E81 : Formula := replace 0 8 equivalentFormula

/-- Swapping the free input labels by a capture-safe intermediate. -/
theorem specialized_syntax : replace 0 1 (replace 1 8 sourceBody) =
    .imp (namedSymmetryCandidate 1) (.imp E18 E81) := by decide

/-- Actual K symmetry at 1,8 with the literal candidate guard at 1. -/
def symmetry_18 : KDerivation
    (imp (candidateCode 1 37 32 33 34 30 35 10 36)
      (imp E18.encode E81.encode)) := by
  have h : KDerivation sourceBody.encode := by
    simpa only [sourceBody, Formula.encode, named_candidate_code,
      PASoundness.PAtoCompactPartialInverseAtSource.named_candidate_code] using candidate_symmetry_closed
  have h8 := universalInstance 1 8 sourceBody (by decide) (by decide) (by decide)
  have d8 : KDerivation (replace 1 8 sourceBody).encode := .mp (.generalize 1 h) h8
  have h1 := universalInstance 0 1 (replace 1 8 sourceBody) (by decide) (by decide) (by decide)
  have d1 : KDerivation (replace 0 1 (replace 1 8 sourceBody)).encode := .mp (.generalize 0 d8) h1
  rw [specialized_syntax] at d1
  exact d1

theorem symmetry_18_certificate : theoremCode (certificate symmetry_18) =
    imp (candidateCode 1 37 32 33 34 30 35 10 36) (imp E18.encode E81.encode) :=
  certificate_correct symmetry_18

end PASoundness.PAtoCompactChainSymmetry

#print axioms PASoundness.PAtoCompactChainSymmetry.symmetry_18
#print axioms PASoundness.PAtoCompactChainSymmetry.symmetry_18_certificate
