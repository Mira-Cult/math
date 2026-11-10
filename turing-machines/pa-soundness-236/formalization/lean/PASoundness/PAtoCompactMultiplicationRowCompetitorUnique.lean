import PASoundness.PAtoCompactMultiplicationSuffixCleanInjective41
import PASoundness.PAtoCompactMultiplicationRowQueryCompetitorFull

/-! Pointwise uniqueness of a new-row competitor at the output of a supplied
clean suffix-map edge. The queried and row descriptions refer to the same
outer graph member. This does not build a product graph or prove its complete
reverse clause. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationRowCompetitorUnique
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactMultiplicationSuffixInjective41
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
open PASoundness.PAtoCompactMultiplicationSuffixCleanInjective41
open PASoundness.PAtoCompactMultiplicationRowQueryCompetitor
open PASoundness.PAtoCompactMultiplicationRowQueryCompetitorFull
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Under clean map bijectivity and an F-edge from selected source 41 to
output 5, the queried row competitor has major 30 and minor 41. The explicit
pair descriptions and row witness share the same outer graph member 63. -/
def row_competitor_unique : KDerivation (imp suffixClean.encode
    (imp suffixBijection.encode (imp (graphFormula 6 41 5).encode
      (imp competitorPairs.encode (imp (replace 9 63 (replace 0 31 rowWitness)).encode
        (both (equal 7 30) (equal 8 41))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(replace 9 63 (replace 0 31 rowWitness)).encode,competitorPairs.encode,
    (graphFormula 6 41 5).encode,suffixBijection.encode,suffixClean.encode]
  have hr : Context Γ (replace 9 63 (replace 0 31 rowWitness)).encode := .head _ _
  have hq : Context Γ competitorPairs.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ (graphFormula 6 41 5).encode := .hypothesis (by simp [Γ])
  have hb : Context Γ suffixBijection.encode := .hypothesis (by simp [Γ])
  have hc : Context Γ suffixClean.encode := .hypothesis (by simp [Γ])
  have hres : Context Γ competitorResult.encode := .mp hr (.mp hq (.closed row_query_full_prefix))
  have hres' : Context Γ (both (equal 7 30) (both (member 31 8) (graphFormula 6 8 5).encode)) := by
    simpa [competitorResult,namedBoth,Formula.not,Formula.encode,both,neg] using hres
  have hmajor := Context.conjunctionLeft hres'
  have hedge := Context.conjunctionRight (Context.conjunctionRight hres')
  have hminor : Context Γ (equal 41 8) :=
    .mp hedge (.mp hf (.mp hb (.mp hc (.closed clean_inverse_unique))))
  exact Context.conjunctionIntro hmajor (Context.eqSymm hminor)

theorem row_competitor_unique_certificate : theoremCode (certificate row_competitor_unique) =
    imp suffixClean.encode (imp suffixBijection.encode (imp (graphFormula 6 41 5).encode
      (imp competitorPairs.encode (imp (replace 9 63 (replace 0 31 rowWitness)).encode
        (both (equal 7 30) (equal 8 41)))))) := certificate_correct row_competitor_unique
end PASoundness.PAtoCompactMultiplicationRowCompetitorUnique
#print axioms PASoundness.PAtoCompactMultiplicationRowCompetitorUnique.row_competitor_unique
#print axioms PASoundness.PAtoCompactMultiplicationRowCompetitorUnique.row_competitor_unique_certificate
