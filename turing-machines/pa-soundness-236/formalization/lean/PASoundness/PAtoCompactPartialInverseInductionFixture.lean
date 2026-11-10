import PASoundness.PAtoCompactPartialInverseFixtureNames
import PASoundness.PAtoCompactCandidateGlobalInduction

/-! Exact partial-inverse specialization of the conditional candidate
induction theorem. The global step and base remain explicit K antecedents.
This does not by itself construct an inverse graph. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseInductionFixture
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateGlobalInduction
open PASoundness.PAtoCompactPartialInversePredicate PASoundness.PAtoCompactPartialInverseFixtureNames
open PASoundness.PAtoCompactUniformBase PASoundness.PAtoCompactQuantifiedRefutation

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The concrete partial-inverse induction instance, retaining exactly the
base and strong global-step schemata as object-level antecedents. -/
def fixed_induction : KDerivation
    (imp (candidateCode 8 37 32 33 34 30 35 10 36)
      (imp (uniformBaseCode 30 10 9 predicate)
        (imp (allCode 31 (allStepsCode 31 30 8 10 15 32 33 predicate))
          (replace 30 8 predicate).encode))) := by
  have h := candidate_global_induction
    8 31 30 34 35 8 10 36 9 15 32 33 38 39 37 40 41 42
    43 44 45 46 47 48 49 51 50 predicate
    chosen_successor_fresh selector_guards.1 selector_guards.2
    fresh_nonempty fresh_induction fresh_domain fresh_outer fresh_alpha
    (by decide) (by decide) induction_name_unbound instance_name_unbound
    filter_avoids_aux.1 filter_avoids_predicate
    (by decide) (by decide) (by decide) (by decide)
    predicate_aux_fresh.1 predicate_aux_fresh.2
    (by decide) (by decide) (by decide)
    filter_avoids_aux.2.1 filter_avoids_aux.2.2
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    graph_aux_fresh filter_base_fresh filter_step_fresh filter_class_fresh
    container_base_fresh container_instance_fresh
  exact h

theorem fixed_induction_certificate :
    theoremCode (certificate fixed_induction) =
      imp (candidateCode 8 37 32 33 34 30 35 10 36)
        (imp (uniformBaseCode 30 10 9 predicate)
          (imp (allCode 31 (allStepsCode 31 30 8 10 15 32 33 predicate))
            (replace 30 8 predicate).encode)) :=
  certificate_correct fixed_induction

end PASoundness.PAtoCompactPartialInverseInductionFixture

#print axioms PASoundness.PAtoCompactPartialInverseInductionFixture.fixed_induction
#print axioms PASoundness.PAtoCompactPartialInverseInductionFixture.fixed_induction_certificate
