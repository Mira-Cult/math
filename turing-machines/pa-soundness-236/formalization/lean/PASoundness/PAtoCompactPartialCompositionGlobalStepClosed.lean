import PASoundness.PAtoCompactPartialCompositionGuardedGlobalStep
import PASoundness.PAtoCompactPartialCompositionInsidePredicate

/-! Strong candidate-induction step for the partial-composition predicate,
combining the actual inside- and outside-source successor proofs. Both input
bijections remain object-level antecedents; this does not itself apply
candidate induction or establish a composition graph. -/
namespace PASoundness.PAtoCompactPartialCompositionGlobalStepClosed
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactQuantifiedRefutation PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityEdgeForward
open PASoundness.PAtoCompactPartialCompositionPredicate
open PASoundness.PAtoCompactPartialCompositionGuardedGlobalStep
open PASoundness.PAtoCompactPartialCompositionInsidePredicate

/-- The exact strong global step, derived with no supplied metatheoretic
inside-branch proof parameter. -/
def global_step : KDerivation (imp bijectionFormula.encode (imp secondBijection.encode
    (allCode 31 (allStepsCode 31 30 10 13 15 32 33 predicate)))) :=
  guarded_global_step_of_inside inside_predicate_step

theorem global_step_certificate : theoremCode (certificate global_step) =
    imp bijectionFormula.encode (imp secondBijection.encode
      (allCode 31 (allStepsCode 31 30 10 13 15 32 33 predicate))) :=
  certificate_correct global_step

end PASoundness.PAtoCompactPartialCompositionGlobalStepClosed

#print axioms PASoundness.PAtoCompactPartialCompositionGlobalStepClosed.global_step
#print axioms PASoundness.PAtoCompactPartialCompositionGlobalStepClosed.global_step_certificate
