import PASoundness.PAtoCompactCandidateAlpha
import PASoundness.PAtoCompactCandidateExact

/-! Extract candidate transitivity at any explicitly fresh pair of test
labels. The object-level candidate code and syntactic freshness remain
explicit; this does not assert candidate existence. -/
namespace PASoundness.PAtoCompactCandidateTransitiveTests

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactCandidateAlpha

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The candidate's own transitivity field is renamed inside K to the
specified distinct test labels; no semantic argument is used. -/
def candidate_transitive_tests (x b p q a k l m g s t : Nat)
    (fresh : [x,p,q,s,t].Nodup) : KDerivation
    (imp (candidateCode x b p q a k l m g) (transitiveCode x s t)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [candidateCode x b p q a k l m g]
  have hc : Context Γ (candidateCode x b p q a k l m g) := .head _ _
  have hl : Context Γ (oneLevelTransitiveCode x b p q) := Context.conjunctionLeft hc
  have ht : Context Γ (transitiveCode x p q) := Context.conjunctionLeft hl
  exact .mp ht (.closed (transitive_rename x p q s t fresh))

theorem candidate_transitive_tests_certificate (x b p q a k l m g s t : Nat)
    (fresh : [x,p,q,s,t].Nodup) : theoremCode (certificate
      (candidate_transitive_tests x b p q a k l m g s t fresh)) =
        imp (candidateCode x b p q a k l m g) (transitiveCode x s t) :=
  certificate_correct (candidate_transitive_tests x b p q a k l m g s t fresh)

end PASoundness.PAtoCompactCandidateTransitiveTests

#print axioms PASoundness.PAtoCompactCandidateTransitiveTests.candidate_transitive_tests
#print axioms PASoundness.PAtoCompactCandidateTransitiveTests.candidate_transitive_tests_certificate
