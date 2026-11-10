import PASoundness.PAtoCompactMultiplicationRestrictedInductionInstance
import PASoundness.PAtoCompactMultiplicationInductionZeroBase

/-! The zero base of first-factor, candidate-restricted multiplication
induction, and its composition with the exact induction instance. The global
candidate-restricted successor schema remains an explicit K antecedent. This
module does not establish multiplication totality or PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationRestrictedInductionBase
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactUniformBase PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactMultiplicationRestrictedInductionInstance
open PASoundness.PAtoCompactMultiplicationInductionZeroBase
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private theorem replaced_predicate : (replace 31 205 predicate).encode =
    imp (domainAt 300 30).encode
      (existsCode 32 (andF (domainAt 300 32) (mulAt 300 205 30 32)).encode) := by
  have h : replace 31 205 predicate = .imp (domainAt 300 30)
      (.ex 32 (andF (domainAt 300 32) (mulAt 300 205 30 32))) := by decide
  rw [h]
  rfl

/-- K proves the exact uniform zero base; the second-factor domain guard is
retained as a hypothesis inside the predicate. -/
def uniform_base : KDerivation (uniformBaseCode 31 205 207 predicate) := by
  apply KDerivation.generalize 205
  rw [replaced_predicate]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(domainAt 300 30).encode, zeroCode 205 207]
  have hz : Context Γ (zeroCode 205 207) := .hypothesis (by simp [Γ])
  exact .mp hz (.closed zero_left_fixed)

/-- With the zero base discharged, the displayed output predicate follows
from the candidate condition and the still-explicit restricted step schema. -/
def multiplication_from_restricted_step : KDerivation
    (imp (candidateCode 200 213 209 210 202 31 203 205 206)
      (imp (allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 205 206)
        (allStepsCode 201 31 204 205 208 209 210 predicate)))
        (replace 31 200 predicate).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 205 206)
    (allStepsCode 201 31 204 205 208 209 210 predicate)),
    candidateCode 200 213 209 210 202 31 203 205 206]
  have hs : Context Γ (allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 205 206)
      (allStepsCode 201 31 204 205 208 209 210 predicate))) := .head _ _
  have hd : Context Γ (candidateCode 200 213 209 210 202 31 203 205 206) :=
    .hypothesis (by simp [Γ])
  exact .mp hs (.mp (.closed uniform_base) (.mp hd (.closed fixed_induction)))

theorem uniform_base_certificate : theoremCode (certificate uniform_base) =
    uniformBaseCode 31 205 207 predicate := certificate_correct uniform_base

theorem multiplication_from_restricted_step_certificate :
    theoremCode (certificate multiplication_from_restricted_step) =
      imp (candidateCode 200 213 209 210 202 31 203 205 206)
        (imp (allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 205 206)
          (allStepsCode 201 31 204 205 208 209 210 predicate)))
          (replace 31 200 predicate).encode) := certificate_correct multiplication_from_restricted_step
end PASoundness.PAtoCompactMultiplicationRestrictedInductionBase
#print axioms PASoundness.PAtoCompactMultiplicationRestrictedInductionBase.uniform_base
#print axioms PASoundness.PAtoCompactMultiplicationRestrictedInductionBase.multiplication_from_restricted_step
#print axioms PASoundness.PAtoCompactMultiplicationRestrictedInductionBase.uniform_base_certificate
#print axioms PASoundness.PAtoCompactMultiplicationRestrictedInductionBase.multiplication_from_restricted_step_certificate
