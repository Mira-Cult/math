import PASoundness.PAtoCompactProductCleanMembers
import PASoundness.PAtoCompactRestrictionEdgeReverse
import PASoundness.PAtoCompactGraphVacuity19

/-! A filtered product triple is an original triple. This is finite K proof
data under the supplied literal filter; it does not prove edge retention,
product matrix preservation, or multiplication totality. The intended
reading of the three endpoint parameters requires avoiding internal binders. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductFilterReverseTriple
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactProductCleanFilter PASoundness.PAtoCompactProductCleanMembers
open PASoundness.PAtoCompactRestrictionEdgeReverse PASoundness.PAtoCompactGraphVacuity19
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Literal triple shape using an existential name 18 for its inner pair.
Endpoint names must avoid bound names 18–22 for the usual endpoint reading. -/
def tripleAt (g u v w : Nat) : Formula := .ex 18
  (namedBoth (pairFormula 18 u v) (graphFormula g 18 w))

private def namedFilter : Formula := .all 55 (namedFilterBody 6 54 55 (cleanPredicate 55))
private theorem filter_code : namedFilter.encode = filterCode 54 := by rfl
private def filter_vacuity_18 : KDerivation
    (imp (filterCode 54) (allCode 18 (filterCode 54))) := by
  simpa only [filter_code] using namedFilter.vacuity 18 (by decide)

/-- The given product filter maps every triple in graph 54 back to graph 6.
This syntactic theorem permits any numeric parameters; separate freshness is
needed to interpret them as three free endpoint names. -/
def reverse_triple (u v w : Nat) : KDerivation (imp (filterCode 54)
    (imp (tripleAt 54 u v w).encode (tripleAt 6 u v w).encode)) := by
  let F := filterCode 54
  let A := (namedBoth (pairFormula 18 u v) (graphFormula 54 18 w)).encode
  let B := (namedBoth (pairFormula 18 u v) (graphFormula 6 18 w)).encode
  have hr : KDerivation (imp F (imp (graphFormula 54 18 w).encode
      (graphFormula 6 18 w).encode)) :=
    restricted_edge_source 6 54 55 (cleanPredicate 55).encode 18 w
      (by decide) (by decide) (by decide) filter_vacuity (graph_vacuity_19 6 18 w)
  have hstep : KDerivation (imp F (imp A B)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [A,F]
    have ha : Context Γ A := .head _ _
    have hf : Context Γ F := .hypothesis (by simp [Γ])
    have hp : Context Γ (pairFormula 18 u v).encode := Context.conjunctionLeft ha
    have hg : Context Γ (graphFormula 54 18 w).encode := Context.conjunctionRight ha
    have ho : Context Γ (graphFormula 6 18 w).encode := .mp hg (.mp hf (.closed hr))
    simpa [B,namedBoth,Formula.encode,both,neg] using Context.conjunctionIntro hp ho
  have h := conditionalExistsCongr 18 filter_vacuity_18 hstep
  simpa [tripleAt,A,B,Formula.encode] using h

theorem reverse_triple_certificate (u v w : Nat) :
    theoremCode (certificate (reverse_triple u v w)) =
      imp (filterCode 54) (imp (tripleAt 54 u v w).encode (tripleAt 6 u v w).encode) :=
  certificate_correct (reverse_triple u v w)
end PASoundness.PAtoCompactProductFilterReverseTriple
#print axioms PASoundness.PAtoCompactProductFilterReverseTriple.reverse_triple
#print axioms PASoundness.PAtoCompactProductFilterReverseTriple.reverse_triple_certificate
