import PASoundness.PAtoCompactRestrictionEdgeReverseClosed
import PASoundness.PAtoCompactRestrictionFresh19
import PASoundness.PAtoCompactTransitiveClosure

/-! Transfer the source guard and graph edge from a supplied endpoint
restriction to its original graph. Negation and existence retain K's
literal encoding, with code 1 = `member 0 0`. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedBackwardGuard
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactRestrictionFilterVacuity
open PASoundness.PAtoCompactRestrictionEdgeReverseClosed PASoundness.PAtoCompactRestrictionFresh19
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Given raw S(2,0) and the displayed endpoint restriction of graph 6 to
graph 8, K derives the universal guard conversion for target name 3. Every
restricted edge from an old-source member 4∈2 is also an original edge
whose source lies in 0. Binder 4 is generalized with explicit vacuity of
both hypotheses; the fixed labels may denote coincident objects. This does
not establish graph coverage, uniqueness, or any quotient property. -/
def backward_guard : KDerivation
    (imp (successorCode 2 0 9)
      (imp (filterGraph 6 8 14 (edgePredicate 14 2 5).encode)
        (allCode 4 (imp (both (member 2 4) (graphFormula 8 4 3).encode)
          (both (member 0 4) (graphFormula 6 4 3).encode))))) := by
  let S := successorCode 2 0 9
  let F := filterGraph 6 8 14 (edgePredicate 14 2 5).encode
  let A := both (member 2 4) (graphFormula 8 4 3).encode
  let C := both (member 0 4) (graphFormula 6 4 3).encode
  let Γ := [F,S]
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 4 z)) := by
    intro z hz
    have hcases : z = F ∨ z = S := by simpa [Γ] using hz
    by_cases he : z = F
    · subst z
      exact restriction_filter_vacuity 6 8 14 2 5 4 (by decide)
    have he : z = S := by simp_all
    subst z
    exact successor_vacuity 2 0 9 4 (by decide) (by decide) (by decide)
  have hlocal : Context Γ (imp A C) := by
    apply Context.deduction
    let Δ := A :: Γ
    have ha : Context Δ A := .head _ _
    have hm : Context Δ (member 2 4) := Context.conjunctionLeft ha
    have hg : Context Δ (graphFormula 8 4 3).encode := Context.conjunctionRight ha
    have hf : Context Δ F := .hypothesis (by simp [Δ,Γ])
    have hs : Context Δ S := .hypothesis (by simp [Δ,Γ])
    have hm' : Context Δ (member 0 4) :=
      .mp (Context.disjunctionRight hm)
        (.mp hs (.closed (successor_include 2 0 9 4 (by decide) (by decide) (by decide))))
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
  exact hall

theorem backward_guard_certificate : theoremCode (certificate backward_guard) =
    imp (successorCode 2 0 9)
      (imp (filterGraph 6 8 14 (edgePredicate 14 2 5).encode)
        (allCode 4 (imp (both (member 2 4) (graphFormula 8 4 3).encode)
          (both (member 0 4) (graphFormula 6 4 3).encode)))) :=
  certificate_correct backward_guard

end PASoundness.PAtoCompactRestrictedBackwardGuard

#print axioms PASoundness.PAtoCompactRestrictedBackwardGuard.backward_guard
#print axioms PASoundness.PAtoCompactRestrictedBackwardGuard.backward_guard_certificate
