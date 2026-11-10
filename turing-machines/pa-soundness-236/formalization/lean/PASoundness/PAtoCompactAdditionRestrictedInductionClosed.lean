import PASoundness.PAtoCompactAdditionRestrictedInductionInstance
import PASoundness.PAtoCompactAdditionInductionUniformBase

/-! Candidate-restricted induction for addition-output existence, with the
exact uniform zero base discharged. The candidate-restricted successor schema
remains an explicit antecedent. This is not addition totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionRestrictedInductionClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactAdditionCandidateInductionInstance (predicate)
open PASoundness.PAtoCompactAdditionInductionUniformBase (uniform_base)
open PASoundness.PAtoCompactAdditionRestrictedInductionInstance (fixed_induction)
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The displayed candidate output-existence conclusion follows from the
candidate condition and the explicit step schema guarded by a candidate
container. The zero base is the independently constructed K derivation. -/
def addition_from_restricted_step : KDerivation
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

theorem addition_from_restricted_step_certificate :
    theoremCode (certificate addition_from_restricted_step) =
      imp (candidateCode 200 213 209 210 202 31 203 205 206)
        (imp (allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 205 206)
          (allStepsCode 201 31 204 205 208 209 210 predicate)))
          (replace 31 200 predicate).encode) :=
  certificate_correct addition_from_restricted_step
end PASoundness.PAtoCompactAdditionRestrictedInductionClosed
#print axioms PASoundness.PAtoCompactAdditionRestrictedInductionClosed.addition_from_restricted_step
#print axioms PASoundness.PAtoCompactAdditionRestrictedInductionClosed.addition_from_restricted_step_certificate
