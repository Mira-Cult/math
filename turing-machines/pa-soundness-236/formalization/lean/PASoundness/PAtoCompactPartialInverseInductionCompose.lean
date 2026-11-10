import PASoundness.PAtoCompactPartialInverseGlobalStepClosed
import PASoundness.PAtoCompactPartialInverseBaseTen
import PASoundness.PAtoCompactCandidateExact

/-! Composition of the exact partial-inverse base and global step with a
supplied literal candidate-induction proof. This isolates the candidate
freshness fixture, which remains explicit proof data; no quotient or PA
translation is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseInductionCompose
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactPartialInverseBase PASoundness.PAtoCompactPartialInversePredicate
open PASoundness.PAtoCompactPartialInverseGlobalStepClosed PASoundness.PAtoCompactPartialInverseBaseTen
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactQuantifiedRefutation
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def candidatePrefix : Nat := candidateCode 8 37 32 33 34 30 35 10 36

def inductionPremise : Nat := imp candidatePrefix
  (imp (uniformBaseCode 30 10 9 predicate)
    (imp (allCode 31 (allStepsCode 31 30 8 10 15 32 33 predicate))
      (replace 30 8 predicate).encode))

/-- The checked zero base and global step discharge the exact induction
schema premises, conditional only on the supplied finite K induction proof. -/
def candidate_inverse_from_induction (hi : KDerivation inductionPremise) : KDerivation
    (imp bijectionFormula.encode (imp candidatePrefix (existsCode 7 partialInverse.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [candidatePrefix,bijectionFormula.encode]
  have hd : Context Γ candidatePrefix := Context.head _ _
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hbase : Context Γ (uniformBaseCode 30 10 9 predicate) := .closed exact_uniform_base
  have hstep : Context Γ (allCode 31 (allStepsCode 31 30 8 10 15 32 33 predicate)) :=
    .mp hb (.closed guarded_global_step)
  have hf : Context Γ (replace 30 8 predicate).encode :=
    .mp hstep (.mp hbase (.mp hd (.closed hi)))
  rw [instance_roundtrip] at hf
  exact hf

theorem candidate_inverse_from_induction_certificate (hi : KDerivation inductionPremise) :
    theoremCode (certificate (candidate_inverse_from_induction hi)) =
      imp bijectionFormula.encode (imp candidatePrefix (existsCode 7 partialInverse.encode)) :=
  certificate_correct (candidate_inverse_from_induction hi)

end PASoundness.PAtoCompactPartialInverseInductionCompose

#print axioms PASoundness.PAtoCompactPartialInverseInductionCompose.candidate_inverse_from_induction
#print axioms PASoundness.PAtoCompactPartialInverseInductionCompose.candidate_inverse_from_induction_certificate
