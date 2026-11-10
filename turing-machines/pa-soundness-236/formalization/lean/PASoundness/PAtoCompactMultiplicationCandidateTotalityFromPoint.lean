import PASoundness.PAtoCompactMultiplicationExactRestrictedStep
import PASoundness.PAtoCompactMultiplicationCandidateTotalityFromStep

/-! Candidate multiplication-output existence from a supplied pointwise
preservation proof. This composes the already proved zero base and restricted
induction with quantification of the pointwise step. The pointwise proof is
an explicit input: it is not supplied by this module. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationCandidateTotalityFromPoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactMultiplicationExactRestrictedStep
open PASoundness.PAtoCompactMultiplicationCandidateTotalityFromStep
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Given the displayed finite K pointwise successor proof, candidate inputs
200 and 30 have a candidate product output 32. -/
def candidate_totality_from_point (hpoint : KDerivation pointCode) :
    KDerivation (imp (domainAt 300 200).encode (imp (domainAt 300 30).encode
      (existsCode 32 (andF (domainAt 300 32) (mulAt 300 200 30 32)).encode))) :=
  candidate_totality_from_step (exact_step_of_point hpoint)

theorem candidate_totality_from_point_certificate (hpoint : KDerivation pointCode) :
    theoremCode (certificate (candidate_totality_from_point hpoint)) =
      imp (domainAt 300 200).encode (imp (domainAt 300 30).encode
        (existsCode 32 (andF (domainAt 300 32) (mulAt 300 200 30 32)).encode)) :=
  certificate_correct (candidate_totality_from_point hpoint)
end PASoundness.PAtoCompactMultiplicationCandidateTotalityFromPoint
#print axioms PASoundness.PAtoCompactMultiplicationCandidateTotalityFromPoint.candidate_totality_from_point
#print axioms PASoundness.PAtoCompactMultiplicationCandidateTotalityFromPoint.candidate_totality_from_point_certificate
