import PASoundness.PAtoCompactPartialCompositionInductionFixture
import PASoundness.PAtoCompactPartialCompositionBaseThirteen
import PASoundness.PAtoCompactPartialCompositionPredicateInstances
import PASoundness.PAtoCompactConditionalTransitivityMatrix

/-! Compose the proved candidate-induction instance and zero base with a
supplied literal K strong-step proof. The two input bijections remain explicit
object-level hypotheses. No strong step, graph collection, or quotient
transitivity is established in this module. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionInductionCompose
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactPartialCompositionPredicate
open PASoundness.PAtoCompactPartialCompositionPredicateInstances
open PASoundness.PAtoCompactPartialCompositionInductionFixture
open PASoundness.PAtoCompactPartialCompositionBaseThirteen
open PASoundness.PAtoCompactConditionalTransitivityMatrix
open PASoundness.PAtoCompactUniformBase PASoundness.PAtoCompactQuantifiedRefutation
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def candidatePrefix : Nat := candidateCode 25 37 32 33 34 30 35 13 36
def globalStep : Nat := allCode 31 (allStepsCode 31 30 10 13 15 32 33 predicate)

/-- The established K induction and zero base transport a supplied K global
step into a represented partial graph for an explicitly candidate prefix. -/
def candidate_composition_of_step
    (step : KDerivation (imp bijectionFormula.encode (imp secondBijection.encode globalStep))) :
    KDerivation (imp bijectionFormula.encode (imp secondBijection.encode
      (imp candidatePrefix (existsCode 9 (replace 10 25
        PASoundness.PAtoCompactPartialCompositionBase.partialComposition).encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [candidatePrefix,secondBijection.encode,bijectionFormula.encode]
  have hd : Context Γ candidatePrefix := Context.head _ _
  have hs : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hbase : Context Γ (uniformBaseCode 30 13 11 predicate) := .closed exact_uniform_base
  have hstep : Context Γ globalStep := .mp hs (.mp hf (.closed step))
  have hi : Context Γ (replace 30 25 predicate).encode :=
    .mp hstep (.mp hbase (.mp hd (.closed fixed_induction)))
  rw [candidate_instance] at hi
  exact hi

theorem candidate_composition_of_step_certificate
    (step : KDerivation (imp bijectionFormula.encode (imp secondBijection.encode globalStep))) :
    theoremCode (certificate (candidate_composition_of_step step)) =
      imp bijectionFormula.encode (imp secondBijection.encode
        (imp candidatePrefix (existsCode 9 (replace 10 25
          PASoundness.PAtoCompactPartialCompositionBase.partialComposition).encode))) :=
  certificate_correct (candidate_composition_of_step step)

end PASoundness.PAtoCompactPartialCompositionInductionCompose

#print axioms PASoundness.PAtoCompactPartialCompositionInductionCompose.candidate_composition_of_step
#print axioms PASoundness.PAtoCompactPartialCompositionInductionCompose.candidate_composition_of_step_certificate
