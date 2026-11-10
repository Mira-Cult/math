import PASoundness.PAtoCompactAdditionCandidateInductionInstance
import PASoundness.PAtoCompactAdditionZeroAllocated
import PASoundness.PAtoCompactDomainClassification

/-! The exact zero base for the guarded addition-output induction predicate.
The finite K proof specializes the previously constructed right-zero output,
then alpha-converts the zero-test binder. This does not establish the global
successor step or addition totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionInductionUniformBase
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactAdditionCandidateInductionInstance
open PASoundness.PAtoCompactAdditionZeroCandidateOutput
open PASoundness.PAtoCompactAdditionZeroAllocated PASoundness.PAtoCompactDomainClassification
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactQuantifiedRefutation
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def fixedBody : Formula := .imp (domainAt 100 30)
  (.imp (.all 36 (.imp (.member 31 36) .bottom)) (.ex 32 outputBody))

private theorem fixedBody_code : fixedBody.encode =
    imp (domainAt 100 30).encode (imp (zeroCode 31 36) (existsCode 32 outputBody.encode)) := by rfl

private theorem replacedBody_code : (replace 31 205 fixedBody).encode =
    imp (domainAt 100 30).encode
      (imp (zeroCode 205 36)
        (existsCode 32 (andF (domainAt 100 32) (replace 31 205 additionFormula)).encode)) := by
  have h : replace 31 205 fixedBody = .imp (domainAt 100 30)
      (.imp (.all 36 (.imp (.member 205 36) .bottom))
        (.ex 32 (andF (domainAt 100 32) (replace 31 205 additionFormula)))) := by decide
  rw [h]
  rfl

private theorem replacedPredicate_code : (replace 31 205 predicate).encode =
    imp (domainAt 100 30).encode
      (existsCode 32 (andF (domainAt 100 32) (replace 31 205 additionFormula)).encode) := by
  have h : replace 31 205 predicate = .imp (domainAt 100 30)
      (.ex 32 (andF (domainAt 100 32) (replace 31 205 additionFormula))) := by decide
  rw [h]
  rfl

private def specialize : KDerivation ((replace 31 205 fixedBody).encode) := by
  have h : KDerivation fixedBody.encode := by rw [fixedBody_code]; exact guarded_fixed_right_zero
  exact .mp (.generalize 31 h) (universalInstance 31 205 fixedBody (by decide) (by decide) (by decide))

/-- The global candidate-induction base: any named zero satisfies the guarded
right-zero output predicate. No first-summand candidate is assumed externally;
it remains an antecedent inside the predicate. -/
def uniform_base : KDerivation (uniformBaseCode 31 205 207 predicate) := by
  apply KDerivation.generalize 205
  rw [replacedPredicate_code]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(domainAt 100 30).encode,zeroCode 205 207]
  have hd : Context Γ (domainAt 100 30).encode := .head _ _
  have hz : Context Γ (zeroCode 205 207) := .hypothesis (by simp [Γ])
  have hz' : Context Γ (zeroCode 205 36) :=
    .mp hz (.closed (zero_test_rename 205 207 36 (by decide) (by decide) (by decide)))
  have hi : KDerivation (imp (domainAt 100 30).encode
      (imp (zeroCode 205 36)
        (existsCode 32 (andF (domainAt 100 32) (replace 31 205 additionFormula)).encode))) := by
    simpa only [replacedBody_code] using specialize
  exact .mp hz' (.mp hd (.closed hi))

/-- The exact candidate induction instance now needs only its global
successor-step schema. That schema remains an explicit K antecedent. -/
def addition_from_step : KDerivation
    (imp (candidateCode 200 213 209 210 202 31 203 205 206)
      (imp (allCode 201 (allStepsCode 201 31 204 205 208 209 210 predicate))
        (replace 31 200 predicate).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [allCode 201 (allStepsCode 201 31 204 205 208 209 210 predicate),
    candidateCode 200 213 209 210 202 31 203 205 206]
  have hs : Context Γ (allCode 201 (allStepsCode 201 31 204 205 208 209 210 predicate)) := .head _ _
  have hd : Context Γ (candidateCode 200 213 209 210 202 31 203 205 206) := .hypothesis (by simp [Γ])
  exact .mp hs (.mp (.closed uniform_base) (.mp hd (.closed fixed_induction)))

theorem addition_from_step_certificate : theoremCode (certificate addition_from_step) =
    imp (candidateCode 200 213 209 210 202 31 203 205 206)
      (imp (allCode 201 (allStepsCode 201 31 204 205 208 209 210 predicate))
        (replace 31 200 predicate).encode) := certificate_correct addition_from_step

theorem uniform_base_certificate : theoremCode (certificate uniform_base) =
    uniformBaseCode 31 205 207 predicate := certificate_correct uniform_base
end PASoundness.PAtoCompactAdditionInductionUniformBase
#print axioms PASoundness.PAtoCompactAdditionInductionUniformBase.uniform_base
#print axioms PASoundness.PAtoCompactAdditionInductionUniformBase.uniform_base_certificate
#print axioms PASoundness.PAtoCompactAdditionInductionUniformBase.addition_from_step
#print axioms PASoundness.PAtoCompactAdditionInductionUniformBase.addition_from_step_certificate
