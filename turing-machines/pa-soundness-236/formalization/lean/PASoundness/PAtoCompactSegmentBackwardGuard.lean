import PASoundness.PAtoCompactRestrictionEdgeReverseClosed
import PASoundness.PAtoCompactRestrictionFresh19
import PASoundness.PAtoCompactTransitiveClosure

/-! Guard transfer for a supplied initial-segment graph restriction. Both
source transitivity and source-endpoint membership remain explicit; no graph
coverage or quotient law is asserted. Compact negation retains literal code 1. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSegmentBackwardGuard
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactRestrictionFilterVacuity
open PASoundness.PAtoCompactRestrictionEdgeReverseClosed PASoundness.PAtoCompactRestrictionFresh19
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Under transitivity of source 0, endpoint 2 in source 0, and the supplied
endpoint filter, every restricted edge from an element of 2 is also an
original edge from an element of 0. The numeric labels are distinct syntactic
names; their denoted objects may coincide. -/
def segment_backward_guard : KDerivation
    (imp (transitiveCode 0 11 12) (imp (member 0 2)
      (imp (filterGraph 6 8 14 (edgePredicate 14 2 5).encode)
        (allCode 4 (imp (both (member 2 4) (graphFormula 8 4 3).encode)
          (both (member 0 4) (graphFormula 6 4 3).encode)))))) := by
  let T := transitiveCode 0 11 12
  let M := member 0 2
  let F := filterGraph 6 8 14 (edgePredicate 14 2 5).encode
  let A := both (member 2 4) (graphFormula 8 4 3).encode
  let C := both (member 0 4) (graphFormula 6 4 3).encode
  let Γ := [F,M,T]
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 4 z)) := by
    intro z hz
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases he : z = F
    · subst z
      exact restriction_filter_vacuity 6 8 14 2 5 4 (by decide)
    by_cases he : z = M
    · subst z
      exact membershipVacuity 0 2 4 (by decide) (by decide)
    have he : z = T := by simp_all
    subst z
    exact transitive_vacuity 0 11 12 4 (by decide) (by decide) (by decide)
  have hlocal : Context Γ (imp A C) := by
    apply Context.deduction
    let Δ := A :: Γ
    have ha : Context Δ A := .head _ _
    have hm : Context Δ (member 2 4) := Context.conjunctionLeft ha
    have hg : Context Δ (graphFormula 8 4 3).encode := Context.conjunctionRight ha
    have hf : Context Δ F := .hypothesis (by simp [Δ,Γ])
    have hM : Context Δ M := .hypothesis (by simp [Δ,Γ])
    have ht : Context Δ T := .hypothesis (by simp [Δ,Γ])
    have hm' : Context Δ (member 0 4) :=
      .mp hm (.mp hM (.mp ht (.closed (transitive_chain 0 11 12 2 4
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))))
    have h19 : 19 ∉ (namedFilter 6 8 14 2 5).names :=
      filter_fresh_19 6 8 14 2 5 (by decide)
    have hg' : Context Δ (graphFormula 6 4 3).encode :=
      .mp hg (.mp hf (.closed (restricted_edge_source 6 8 14 2 5 4 3
        (by decide) (by decide) (by decide) h19)))
    exact Context.conjunctionIntro hm' hg'
  have hall : Context Γ (allCode 4 (imp A C)) := Context.generalize 4 hv hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hall

theorem segment_backward_guard_certificate : theoremCode (certificate segment_backward_guard) =
    imp (transitiveCode 0 11 12) (imp (member 0 2)
      (imp (filterGraph 6 8 14 (edgePredicate 14 2 5).encode)
        (allCode 4 (imp (both (member 2 4) (graphFormula 8 4 3).encode)
          (both (member 0 4) (graphFormula 6 4 3).encode))))) :=
  certificate_correct segment_backward_guard

end PASoundness.PAtoCompactSegmentBackwardGuard

#print axioms PASoundness.PAtoCompactSegmentBackwardGuard.segment_backward_guard
#print axioms PASoundness.PAtoCompactSegmentBackwardGuard.segment_backward_guard_certificate
