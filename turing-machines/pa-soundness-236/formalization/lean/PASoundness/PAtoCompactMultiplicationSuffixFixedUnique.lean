import PASoundness.PAtoCompactMultiplicationSuffixCompetitorClosed
import PASoundness.PAtoCompactMultiplicationSuffixCompetitorQuantify
import PASoundness.PAtoCompactFreeVacuity

/-! Quantified competitor uniqueness for the fixed selected suffix preimage.
All graph/filter assumptions, including the map edge (41,5), remain literal
antecedents. This uses the proved pointwise K reflection directly and does not
rename 41 through a binder of the map bijection. This is not a complete product
reverse clause, multiplication totality, or PA soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationSuffixFixedUnique
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactMultiplicationSuffixCompetitorClosed
open PASoundness.PAtoCompactMultiplicationCompetitorTripleLift
open PASoundness.PAtoCompactMultiplicationSuffixCompetitorQuantify
open PASoundness.PAtoCompactMultiplicationSuffixReverseExistence (triple64 reversePreimageBody)
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The reverse-clause uniqueness formula at the fixed selected pair 30,41. -/
def fixedUnique : Formula := replace 4 41 (replace 3 30 uniqueBody)

private theorem competitor_shape : competitorTriple = triple64 7 8 5 := by decide
private theorem fixed_unique_shape : fixedUnique =
    .all 7 (.all 8 (.imp competitor competitorEqualities)) := by decide

/-- From the exact old-graph, suffix, clean-map, and selected map-edge
assumptions, every guarded competing product triple to output 5 has
coordinates 30 and 41. No pointwise K proof is supplied as input. -/
def fixed_unique_of_assumptions : KDerivation (imp assumptions.encode fixedUnique.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [assumptions.encode]
  have ha : Context Γ assumptions.encode := .head _ _
  have hpoint : Context Γ (imp competitor.encode competitorEqualities.encode) := by
    apply Context.deduction
    let Δ := [competitor.encode,assumptions.encode]
    have hq : Context Δ competitor.encode := .head _ _
    have hparts : Context Δ (both (member 38 7)
        (both (member 31 8) (triple64 7 8 5).encode)) := by
      simpa [competitor,reversePreimageBody,namedBoth,Formula.encode,Formula.not,both,neg] using hq
    have ht : Context Δ competitorTriple.encode := by
      rw [competitor_shape]
      exact Context.conjunctionRight (Context.conjunctionRight hparts)
    have ha' : Context Δ assumptions.encode := .hypothesis (by simp [Δ])
    exact .mp ht (.mp ha' (.closed suffix_competitor_unique))
  have hv8 : ∀ a, a ∈ Γ → KDerivation (imp a (allCode 8 a)) := by
    intro a ha'
    have he : a = assumptions.encode := by simpa [Γ] using ha'
    subst a
    exact free_vacuity 8 assumptions (by decide)
  have hv7 : ∀ a, a ∈ Γ → KDerivation (imp a (allCode 7 a)) := by
    intro a ha'
    have he : a = assumptions.encode := by simpa [Γ] using ha'
    subst a
    exact free_vacuity 7 assumptions (by decide)
  have hall8 := Context.generalize 8 hv8 hpoint
  have hall7 := Context.generalize 7 hv7 hall8
  rw [fixed_unique_shape]
  change Context Γ (allCode 7 (allCode 8 (imp competitor.encode competitorEqualities.encode)))
  exact hall7

theorem fixed_unique_of_assumptions_certificate :
    theoremCode (certificate fixed_unique_of_assumptions) =
      imp assumptions.encode fixedUnique.encode := certificate_correct _
end PASoundness.PAtoCompactMultiplicationSuffixFixedUnique
#print axioms PASoundness.PAtoCompactMultiplicationSuffixFixedUnique.fixed_unique_of_assumptions
#print axioms PASoundness.PAtoCompactMultiplicationSuffixFixedUnique.fixed_unique_of_assumptions_certificate
