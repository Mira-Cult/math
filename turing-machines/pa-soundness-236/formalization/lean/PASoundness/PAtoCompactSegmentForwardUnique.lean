import PASoundness.PAtoCompactRestrictedForwardUnique

/-! K uniqueness transfer for an arbitrary initial-segment restriction.
The original target is transitive and contains the restricted target; no
successor or order-isomorphism graph existence is asserted. Literal K
negation uses code 1 (`member 0 0`). -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSegmentForwardUnique
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactRestrictedForwardPoint
open PASoundness.PAtoCompactRestrictionEdgeReverseClosed PASoundness.PAtoCompactRestrictionFresh19
open PASoundness.PAtoCompactRestrictionFilterVacuity PASoundness.PAtoCompactBijectionForwardAtSeven
open PASoundness.PAtoCompactRestrictedForwardUnique
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- In a transitive target 1 containing 5, an edge of the filtered graph
with target in 5 is an old graph edge to a target in 1. -/
def segment_guard_to_original : KDerivation
    (imp (transitiveCode 1 16 18) (imp (member 1 5) (imp filter
      (allCode 4 (imp
        (both (member 5 4) (graphFormula 8 7 4).encode)
        (both (member 1 4) (graphFormula 6 7 4).encode)))))) := by
  let T := transitiveCode 1 16 18
  let M := member 1 5
  let F := filter
  let A := both (member 5 4) (graphFormula 8 7 4).encode
  let B := both (member 1 4) (graphFormula 6 7 4).encode
  let Γ := [F,M,T]
  have hf19 : 19 ∉ (namedFilter 6 8 14 2 5).names :=
    filter_fresh_19 6 8 14 2 5 (by decide)
  have hpoint : Context Γ (imp A B) := by
    apply Context.deduction
    let Δ := A :: Γ
    have ha : Context Δ A := .head _ _
    have hold : Context Δ (member 5 4) := Context.conjunctionLeft ha
    have hedge : Context Δ (graphFormula 8 7 4).encode := Context.conjunctionRight ha
    have ht : Context Δ T := .hypothesis (by simp [Δ,Γ])
    have hm : Context Δ M := .hypothesis (by simp [Δ,Γ])
    have hf : Context Δ F := .hypothesis (by simp [Δ,Γ])
    have hnew : Context Δ (member 1 4) :=
      .mp hold (.mp hm (.mp ht (.closed
        (transitive_chain 1 16 18 5 4 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)))))
    have horig : Context Δ (graphFormula 6 7 4).encode :=
      .mp hedge (.mp hf (.closed
        (restricted_edge_source 6 8 14 2 5 7 4 (by decide) (by decide) (by decide) hf19)))
    exact Context.conjunctionIntro hnew horig
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 4 z)) := by
    intro z hz
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases he : z = F
    · subst z
      simpa only [F, filter] using
        (restriction_filter_vacuity 6 8 14 2 5 4 (by decide))
    by_cases he : z = M
    · subst z
      exact membershipVacuity 1 5 4 (by decide) (by decide)
    have he : z = T := by simp_all
    subst z
    exact transitive_vacuity 1 16 18 4 (by decide) (by decide) (by decide)
  have hall : Context Γ (allCode 4 (imp A B)) := Context.generalize 4 hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hall

/-- Transfer the same chosen old image witness's uniqueness to the
filtered graph, under the target transitivity and top-member hypotheses. -/
def segment_witness_from_original : KDerivation
    (imp (transitiveCode 1 16 18) (imp (member 1 5) (imp filter
      (imp witnessAtSeven.encode
        (imp (both (member 5 3) (graphFormula 8 7 3).encode)
          restrictedWitness.encode))))) := by
  let T := transitiveCode 1 16 18
  let M := member 1 5
  let F := filter
  let W := witnessAtSeven.encode
  let R := both (member 5 3) (graphFormula 8 7 3).encode
  let A := both (member 5 4) (graphFormula 8 7 4).encode
  let B := both (member 1 4) (graphFormula 6 7 4).encode
  let C := equal 4 3
  have hcomp : KDerivation (imp (imp A B) (imp (imp B C) (imp A C))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [A,imp B C,imp A B]
    have ha : Context Γ A := .head _ _
    have hab : Context Γ (imp A B) := .hypothesis (by simp [Γ])
    have hbc : Context Γ (imp B C) := .hypothesis (by simp [Γ])
    exact .mp (.mp ha hab) hbc
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [R,W,F,M,T]
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hm : Context Γ M := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hw : Context Γ W := .hypothesis (by simp [Γ])
  have hr : Context Γ R := .head _ _
  have hg : Context Γ (allCode 4 (imp A B)) :=
    .mp hf (.mp hm (.mp ht (.closed segment_guard_to_original)))
  have hu : Context Γ (allCode 4 (imp B C)) :=
    Context.conjunctionRight (Context.conjunctionRight hw)
  have htransport : Context Γ (allCode 4 (imp (imp B C) (imp A C))) :=
    Context.allMP hg (.closed (.generalize 4 hcomp))
  have hnew : Context Γ (allCode 4 (imp A C)) := Context.allMP hu htransport
  have hmem : Context Γ (member 5 3) := Context.conjunctionLeft hr
  have hedge : Context Γ (graphFormula 8 7 3).encode := Context.conjunctionRight hr
  exact Context.conjunctionIntro hmem (Context.conjunctionIntro hedge hnew)

theorem segment_guard_certificate : theoremCode (certificate segment_guard_to_original) =
    imp (transitiveCode 1 16 18) (imp (member 1 5) (imp filter
      (allCode 4 (imp (both (member 5 4) (graphFormula 8 7 4).encode)
        (both (member 1 4) (graphFormula 6 7 4).encode))))) :=
  certificate_correct segment_guard_to_original

theorem segment_witness_certificate : theoremCode (certificate segment_witness_from_original) =
    imp (transitiveCode 1 16 18) (imp (member 1 5) (imp filter
      (imp witnessAtSeven.encode (imp (both (member 5 3) (graphFormula 8 7 3).encode)
        restrictedWitness.encode)))) := certificate_correct segment_witness_from_original

end PASoundness.PAtoCompactSegmentForwardUnique

#print axioms PASoundness.PAtoCompactSegmentForwardUnique.segment_guard_to_original
#print axioms PASoundness.PAtoCompactSegmentForwardUnique.segment_witness_from_original
