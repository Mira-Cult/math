import PASoundness.PAtoCompactAdditionRestrictedStepInstance
import PASoundness.PAtoCompactCandidateStepBinderTransport

/-! The exact candidate-restricted induction step for the proposed addition
output predicate, conditional on the displayed pointwise K derivation. The
container's bound name is alpha-transported from 231 to 205, as required by
the induction instance. This does not prove the pointwise input, addition
totality, or a PA induction axiom. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionExactRestrictedStep
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactAdditionCandidateInductionInstance
open PASoundness.PAtoCompactAdditionRestrictedStepInstance
open PASoundness.PAtoCompactCandidateStepBinderTransport

/-- A pointwise K proof yields the induction engine's exact candidate-guarded
step schema; the pointwise proof is an explicit input. -/
def exact_step_of_point (hpoint : KDerivation pointCode) : KDerivation
    (allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 205 206)
      (allStepsCode 201 31 204 205 208 209 210 predicate))) := by
  exact .mp (restricted_step_of_point hpoint)
    (restricted_step_witness_transport 201 213 209 210 202 31 203 205 206 231
      31 204 208 predicate (by decide) (by decide))

theorem exact_step_of_point_certificate (hpoint : KDerivation pointCode) :
    theoremCode (certificate (exact_step_of_point hpoint)) =
      allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 205 206)
        (allStepsCode 201 31 204 205 208 209 210 predicate)) :=
  certificate_correct (exact_step_of_point hpoint)
end PASoundness.PAtoCompactAdditionExactRestrictedStep
#print axioms PASoundness.PAtoCompactAdditionExactRestrictedStep.exact_step_of_point
#print axioms PASoundness.PAtoCompactAdditionExactRestrictedStep.exact_step_of_point_certificate
