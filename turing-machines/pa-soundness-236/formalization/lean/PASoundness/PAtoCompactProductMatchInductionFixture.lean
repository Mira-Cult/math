import PASoundness.PAtoCompactProductMatchInductionNames
import PASoundness.PAtoCompactCandidateGlobalInduction

/-! Candidate induction for the concrete partial-match predicate. The
nonempty strong step remains an explicit finite K proof input; no such step
or global graph collection is established here. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchInductionFixture

open PASoundness.CompactProof PASoundness.CompactNamed PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateGlobalInduction
open PASoundness.PAtoCompactUniformBase PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactProductMatchPartialBase PASoundness.PAtoCompactProductMatchInductionNames

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def candidatePrefix : Nat := candidateCode 70 81 77 78 72 64 73 59 75
def globalStep : Nat := allCode 71 (allStepsCode 71 64 74 59 76 77 78 predicate)

/-- The candidate-induction theorem specialized to the partial matching
predicate, with its base and strong step still explicit K antecedents. -/
def fixed_induction : KDerivation
    (imp candidatePrefix (imp (uniformBaseCode 64 59 60 predicate)
      (imp globalStep (replace 64 70 predicate).encode))) := by
  have h := candidate_global_induction
    70 71 64 72 73 74 59 75 60 76 77 78 79 80 81 82 83 84 85 86 87 88 89 90 91 92 93 predicate
    chosen_successor_fresh selector_guards.1 selector_guards.2
    fresh_nonempty fresh_induction fresh_domain fresh_outer fresh_alpha
    (by decide) (by decide) (by decide) (by decide)
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

theorem instance_shape : replace 64 70 predicate = .ex 58 (replace 59 70 partialMatch) := by decide

/-- The proved zero base discharges the base input. The candidate-domain
and strong-step assumptions remain literal object-level antecedents. -/
def prefix_collection_of_step : KDerivation
    (imp candidatePrefix (imp globalStep
      (existsCode 58 (replace 59 70 partialMatch).encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [globalStep,candidatePrefix]
  have hs : Context Γ globalStep := .head _ _
  have hc : Context Γ candidatePrefix := .hypothesis (by simp [Γ])
  have hi : Context Γ (replace 64 70 predicate).encode :=
    .mp hs (.mp (.closed exact_uniform_base) (.mp hc (.closed fixed_induction)))
  rw [instance_shape] at hi
  simpa [Formula.encode] using hi

theorem prefix_collection_of_step_certificate :
    theoremCode (certificate prefix_collection_of_step) =
      imp candidatePrefix (imp globalStep
        (existsCode 58 (replace 59 70 partialMatch).encode)) := certificate_correct _

end PASoundness.PAtoCompactProductMatchInductionFixture

#print axioms PASoundness.PAtoCompactProductMatchInductionFixture.fixed_induction
#print axioms PASoundness.PAtoCompactProductMatchInductionFixture.prefix_collection_of_step
#print axioms PASoundness.PAtoCompactProductMatchInductionFixture.prefix_collection_of_step_certificate
