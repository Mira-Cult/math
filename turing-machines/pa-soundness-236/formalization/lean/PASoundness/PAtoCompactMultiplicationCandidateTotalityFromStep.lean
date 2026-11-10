import PASoundness.PAtoCompactMultiplicationRestrictedInductionBase
import PASoundness.PAtoCompactMultiplicationInductionCandidateBridge

/-! Reduction of candidate-guarded multiplication output existence to the
explicit first-factor restricted successor schema. This is conditional: the
successor schema is supplied as finite K proof data, not established here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationCandidateTotalityFromStep
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactMultiplicationRestrictedInductionInstance
open PASoundness.PAtoCompactMultiplicationRestrictedInductionBase
open PASoundness.PAtoCompactMultiplicationInductionCandidateBridge
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- If the first-factor restricted successor schema has a finite K proof,
then allocated candidates 200 and 30 have a candidate product output 32.
The supplied schema, not Lean's standard-model soundness, is the missing
mathematical input. -/
def candidate_totality_from_step
    (step : KDerivation (allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 205 206)
      (allStepsCode 201 31 204 205 208 209 210 predicate)))) :
    KDerivation (imp (domainAt 300 200).encode (imp (domainAt 300 30).encode
      (existsCode 32 (andF (domainAt 300 32) (mulAt 300 200 30 32)).encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(domainAt 300 30).encode, (domainAt 300 200).encode]
  have hy : Context Γ (domainAt 300 30).encode := .head _ _
  have hx : Context Γ (domainAt 300 200).encode := .hypothesis (by simp [Γ])
  have hd : Context Γ (candidateCode 200 213 209 210 202 31 203 205 206) :=
    .mp hx (.closed induction_candidate_bridge)
  have hi : Context Γ (replace 31 200 predicate).encode :=
    .mp (.closed step) (.mp hd (.closed multiplication_from_restricted_step))
  rw [instance_syntax] at hi
  exact .mp hy hi

theorem candidate_totality_from_step_certificate
    (step : KDerivation (allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 205 206)
      (allStepsCode 201 31 204 205 208 209 210 predicate)))) :
    theoremCode (certificate (candidate_totality_from_step step)) =
      imp (domainAt 300 200).encode (imp (domainAt 300 30).encode
        (existsCode 32 (andF (domainAt 300 32) (mulAt 300 200 30 32)).encode)) :=
  certificate_correct (candidate_totality_from_step step)
end PASoundness.PAtoCompactMultiplicationCandidateTotalityFromStep
#print axioms PASoundness.PAtoCompactMultiplicationCandidateTotalityFromStep.candidate_totality_from_step
#print axioms PASoundness.PAtoCompactMultiplicationCandidateTotalityFromStep.candidate_totality_from_step_certificate
