import PASoundness.PAtoCompactCandidateStepGeneralization
import PASoundness.PAtoCompactCandidateWitness
import PASoundness.PAtoCompactCandidateStepBinderTransport
import PASoundness.PAtoCompactMultiplicationRestrictedInductionInstance

/-! A candidate-restricted multiplication induction step from an explicitly
supplied pointwise K derivation. The container's witness name is alpha
transported from 231 to 205 after generalization. This does not establish the
pointwise step, multiplication totality, or PA proof transport. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationExactRestrictedStep
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateWitness
open PASoundness.PAtoCompactCandidateStepGeneralization PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactQuantifiedRefutation PASoundness.PAtoCompactCandidateStepBinderTransport
open PASoundness.PAtoCompactMultiplicationRestrictedInductionInstance
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def trivial : Formula := .imp (.member 30 30) (.member 30 30)

/-- The explicit pointwise candidate-endpoint preservation obligation for the
multiplication-output predicate. -/
def pointCode : Nat :=
  imp (candidateCode 204 230 209 210 232 31 203 231 206)
    (imp (candidateCode 205 234 209 210 237 31 240 231 206)
      (imp (predecessorCore 201 204 205 208 209 210)
        (imp (replace 31 204 predicate).encode (replace 31 205 predicate).encode)))

/-- A supplied pointwise K proof gives the candidate-restricted step with
fresh intermediate witness name 231. -/
def restricted_step_of_point (hpoint : KDerivation pointCode) : KDerivation
    (allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 231 206)
      (allStepsCode 201 31 204 205 208 209 210 predicate))) := by
  let H := trivial.encode
  have hh : KDerivation H := by
    exact PASoundness.CompactHilbertBasis.identity (member 30 30)
  have hvHy : KDerivation (imp H (allCode 204 H)) := trivial.vacuity 204 (by decide)
  have hvHz : KDerivation (imp H (allCode 205 H)) := trivial.vacuity 205 (by decide)
  have hvHY : KDerivation (imp H (allCode 201 H)) := trivial.vacuity 201 (by decide)
  have hvCy : KDerivation (imp (candidateCode 201 213 209 210 202 31 203 231 206)
      (allCode 204 (candidateCode 201 213 209 210 202 31 203 231 206))) :=
    candidate_vacuity 201 213 209 210 202 31 203 231 206 204 (by decide)
  have hvCz : KDerivation (imp (candidateCode 201 213 209 210 202 31 203 231 206)
      (allCode 205 (candidateCode 201 213 209 210 202 31 203 231 206))) :=
    candidate_vacuity 201 213 209 210 202 31 203 231 206 205 (by decide)
  have hp : KDerivation (imp H pointCode) := Context.closeEmpty (Context.deduction (.closed hpoint))
  exact .mp hh (candidate_restricted_step 201 204 205 208 213 209 210 230
    202 31 203 231 206 232 233 234 235 236 237 238 239 240 241 31 predicate H
    (by decide) (by decide) hvHy hvHz hvHY hvCy hvCz hp)

/-- The same supplied pointwise proof gives the exact restricted step needed
by the multiplication induction instance, with witness name 205. -/
def exact_step_of_point (hpoint : KDerivation pointCode) : KDerivation
    (allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 205 206)
      (allStepsCode 201 31 204 205 208 209 210 predicate))) := by
  exact .mp (restricted_step_of_point hpoint)
    (restricted_step_witness_transport 201 213 209 210 202 31 203 205 206 231
      31 204 208 predicate (by decide) (by decide))

theorem restricted_step_of_point_certificate (hpoint : KDerivation pointCode) :
    theoremCode (certificate (restricted_step_of_point hpoint)) =
      allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 231 206)
        (allStepsCode 201 31 204 205 208 209 210 predicate)) :=
  certificate_correct (restricted_step_of_point hpoint)

theorem exact_step_of_point_certificate (hpoint : KDerivation pointCode) :
    theoremCode (certificate (exact_step_of_point hpoint)) =
      allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 205 206)
        (allStepsCode 201 31 204 205 208 209 210 predicate)) :=
  certificate_correct (exact_step_of_point hpoint)
end PASoundness.PAtoCompactMultiplicationExactRestrictedStep
#print axioms PASoundness.PAtoCompactMultiplicationExactRestrictedStep.restricted_step_of_point
#print axioms PASoundness.PAtoCompactMultiplicationExactRestrictedStep.exact_step_of_point
#print axioms PASoundness.PAtoCompactMultiplicationExactRestrictedStep.restricted_step_of_point_certificate
#print axioms PASoundness.PAtoCompactMultiplicationExactRestrictedStep.exact_step_of_point_certificate
