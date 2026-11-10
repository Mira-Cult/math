import PASoundness.PAtoCompactAdditionRestrictedInductionClosed
import PASoundness.PAtoCompactAdditionExactRestrictedStep

/-! A proof-data reduction from the exact candidate-endpoint pointwise
addition successor obligation to candidate-guarded addition-output existence.
The pointwise K derivation remains an explicit argument. This is not addition
totality or a PA induction translation. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionRestrictedInductionFromPoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactAdditionCandidateInductionInstance (predicate)
open PASoundness.PAtoCompactAdditionRestrictedStepInstance (pointCode)
open PASoundness.PAtoCompactAdditionExactRestrictedStep (exact_step_of_point)
open PASoundness.PAtoCompactAdditionRestrictedInductionClosed (addition_from_restricted_step)
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- An explicit finite K pointwise successor proof supplies the candidate-
restricted induction step, leaving the candidate input as an object-level
antecedent. -/
def addition_from_point (hpoint : KDerivation pointCode) : KDerivation
    (imp (candidateCode 200 213 209 210 202 31 203 205 206)
      (replace 31 200 predicate).encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let D := candidateCode 200 213 209 210 202 31 203 205 206
  have hd : Context [D] D := .head _ _
  exact .mp (.closed (exact_step_of_point hpoint)) (.mp hd (.closed addition_from_restricted_step))

theorem addition_from_point_certificate (hpoint : KDerivation pointCode) :
    theoremCode (certificate (addition_from_point hpoint)) =
      imp (candidateCode 200 213 209 210 202 31 203 205 206)
        (replace 31 200 predicate).encode := certificate_correct (addition_from_point hpoint)
end PASoundness.PAtoCompactAdditionRestrictedInductionFromPoint
#print axioms PASoundness.PAtoCompactAdditionRestrictedInductionFromPoint.addition_from_point
#print axioms PASoundness.PAtoCompactAdditionRestrictedInductionFromPoint.addition_from_point_certificate
