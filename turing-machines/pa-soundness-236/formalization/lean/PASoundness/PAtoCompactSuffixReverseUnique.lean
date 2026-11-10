import PASoundness.PAtoCompactBijectionBackwardAtThree
import PASoundness.PAtoCompactRestrictionSubset
import PASoundness.PAtoCompactRestrictionEdgeReverseClosed
import PASoundness.PAtoCompactRestrictionFresh19
import PASoundness.PAtoCompactFilterInstantiation

/-! Reverse uniqueness for an endpoint-filtered suffix graph. The original
backward witness, source-suffix filter and restricted graph filter remain
explicit; this is not a coverage, graph-existence, or suffix-isomorphism proof. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuffixReverseUnique
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactRestrictionSubset
open PASoundness.PAtoCompactRestrictionFilterVacuity PASoundness.PAtoCompactRestrictionFresh19
open PASoundness.PAtoCompactRestrictionEdgeReverseClosed PASoundness.PAtoCompactBijectionBackwardAtThree
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Source suffix 40 is filtered from outer source 0 by exclusion of cut 2. -/
def sourceFilter : Nat := filterGraph 0 40 42 (neg (member 2 42))
/-- Graph 8 is the restriction of original graph 6 to suffix endpoints 40,41. -/
def graphFilter : Nat := filterGraph 6 8 14 (edgePredicate 14 40 41).encode

private def sourceFilterNamed : Formula :=
  .all 42 (namedFilterBody 0 40 42 ((Formula.member 2 42).not))

private theorem source_filter_code : sourceFilterNamed.encode = sourceFilter := by
  simp [sourceFilterNamed, sourceFilter, namedFilterBody, namedBoth, Formula.not,
    Formula.encode, filterGraph, filterPredicate, CompactProof.both, CompactProof.neg]

private def source_filter_vacuity : KDerivation
    (imp sourceFilter (allCode 4 sourceFilter)) := by
  simpa only [source_filter_code] using sourceFilterNamed.vacuity 4 (by decide)

/-- Every edge of the restricted graph with source in suffix 40 has its
source in outer 0 and is also an edge of the same original graph 6. -/
def suffix_reverse_guard : KDerivation
    (imp sourceFilter (imp graphFilter
      (allCode 4 (imp (both (member 40 4) (graphFormula 8 4 3).encode)
        (both (member 0 4) (graphFormula 6 4 3).encode))))) := by
  let S := sourceFilter
  let F := graphFilter
  let A := both (member 40 4) (graphFormula 8 4 3).encode
  let B := both (member 0 4) (graphFormula 6 4 3).encode
  let Γ := [F,S]
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 4 z)) := by
    intro z hz
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases he : z = F
    · subst z
      exact restriction_filter_vacuity 6 8 14 40 41 4 (by decide)
    have he : z = S := by simp_all
    subst z
    exact source_filter_vacuity
  have hlocal : Context Γ (imp A B) := by
    apply Context.deduction
    let Δ := A :: Γ
    have ha : Context Δ A := .head _ _
    have hs : Context Δ S := .hypothesis (by simp [Δ,Γ])
    have hf : Context Δ F := .hypothesis (by simp [Δ,Γ])
    have hm : Context Δ (member 40 4) := Context.conjunctionLeft ha
    have hg : Context Δ (graphFormula 8 4 3).encode := Context.conjunctionRight ha
    have hm' : Context Δ (member 0 4) :=
      .mp hm (.mp hs (.closed (filter_member_source 0 40 42
        (neg (member 2 42)) 4 (by decide) (by decide) (by decide))))
    have hfresh : 19 ∉ (namedFilter 6 8 14 40 41).names :=
      filter_fresh_19 6 8 14 40 41 (by decide)
    have hg' : Context Δ (graphFormula 6 4 3).encode :=
      .mp hg (.mp hf (.closed (restricted_edge_source 6 8 14 40 41 4 3
        (by decide) (by decide) (by decide) hfresh)))
    exact Context.conjunctionIntro hm' hg'
  have hall : Context Γ (allCode 4 (imp A B)) := Context.generalize 4 hv hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hall

/-- The actual original reverse witness at name 7 remains unique among
suffix-guarded edges of the restricted graph. Syntactic names are fixed;
the objects assigned to those names may coincide. -/
def suffix_reverse_unique : KDerivation
    (imp sourceFilter (imp graphFilter (imp (witness 7).encode
      (allCode 4 (imp (both (member 40 4) (graphFormula 8 4 3).encode)
        (equal 4 7)))))) := by
  let S := sourceFilter
  let F := graphFilter
  let W := (witness 7).encode
  let A := both (member 40 4) (graphFormula 8 4 3).encode
  let B := both (member 0 4) (graphFormula 6 4 3).encode
  let E := equal 4 7
  let Γ := [W,F,S]
  have hcompose : KDerivation (imp (imp A B) (imp (imp B E) (imp A E))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Δ := [A,imp B E,imp A B]
    have ha : Context Δ A := .head _ _
    have hab : Context Δ (imp A B) := .hypothesis (by simp [Δ])
    have hbe : Context Δ (imp B E) := .hypothesis (by simp [Δ])
    exact .mp (.mp ha hab) hbe
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hw : Context Γ W := .head _ _
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hguard : Context Γ (allCode 4 (imp A B)) :=
    .mp hf (.mp hs (.closed suffix_reverse_guard))
  have hold : Context Γ (allCode 4 (imp B E)) :=
    Context.conjunctionRight (Context.conjunctionRight hw)
  have hc : Context Γ (allCode 4 (imp (imp A B) (imp (imp B E) (imp A E)))) :=
    .closed (.generalize 4 hcompose)
  have hnext : Context Γ (allCode 4 (imp (imp B E) (imp A E))) := Context.allMP hguard hc
  exact Context.allMP hold hnext

theorem suffix_reverse_unique_certificate : theoremCode (certificate suffix_reverse_unique) =
    imp sourceFilter (imp graphFilter (imp (witness 7).encode
      (allCode 4 (imp (both (member 40 4) (graphFormula 8 4 3).encode)
        (equal 4 7))))) :=
  certificate_correct suffix_reverse_unique

end PASoundness.PAtoCompactSuffixReverseUnique

#print axioms PASoundness.PAtoCompactSuffixReverseUnique.sourceFilter
#print axioms PASoundness.PAtoCompactSuffixReverseUnique.graphFilter
#print axioms PASoundness.PAtoCompactSuffixReverseUnique.suffix_reverse_guard
#print axioms PASoundness.PAtoCompactSuffixReverseUnique.suffix_reverse_unique
#print axioms PASoundness.PAtoCompactSuffixReverseUnique.suffix_reverse_unique_certificate
