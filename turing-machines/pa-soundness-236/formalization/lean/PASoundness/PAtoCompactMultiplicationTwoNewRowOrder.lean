import PASoundness.PAtoCompactMultiplicationRowQueryFirstExists
import PASoundness.PAtoCompactMultiplicationRowQuerySecondExists
import PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
import PASoundness.PAtoCompactMultiplicationSameRowOrder

/-! The same-row multiplication lexicographic comparisons, using two explicit
new-row query witnesses and a supplied clean ordered suffix graph. The row
branches are hypotheses: no product-graph case split, row collection,
multiplication totality, or PA bridge is asserted. -/
namespace PASoundness.PAtoCompactMultiplicationTwoNewRowOrder
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactMultiplicationRowQueryFirst
open PASoundness.PAtoCompactMultiplicationRowQueryFirstExists
open PASoundness.PAtoCompactMultiplicationRowQuerySecond
open PASoundness.PAtoCompactMultiplicationRowQuerySecondExists
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
open PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder
open PASoundness.PAtoCompactMultiplicationSameRowLex
open PASoundness.PAtoCompactMultiplicationSameRowOrder
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Two explicit new-row edge queries, and a clean order-preserving suffix
map, entail the exact comparisons in both directions. -/
def two_new_row_order : KDerivation (imp suffixOrder.encode (imp suffixClean.encode
    (imp queriedNewRow.encode (imp queriedNewRowSecond.encode
      (both forwardClause reverseClause))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [queriedNewRowSecond.encode,queriedNewRow.encode,suffixClean.encode,suffixOrder.encode]
  have hr2 : Context Γ queriedNewRowSecond.encode := .head _ _
  have hr1 : Context Γ queriedNewRow.encode := .hypothesis (by simp [Γ])
  have hc : Context Γ suffixClean.encode := .hypothesis (by simp [Γ])
  have ho : Context Γ suffixOrder.encode := .hypothesis (by simp [Γ])
  have h1 : Context Γ (both (equal 3 30) (both (member 31 4) (graphFormula 6 4 5).encode)) := by
    have h := Context.mp hr1 (.closed query_exists_elim)
    simpa [queryResult,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have h2 : Context Γ (both (equal 7 30) (both (member 31 8) (graphFormula 6 8 9).encode)) := by
    have h := Context.mp hr2 (.closed query_second_exists_elim)
    simpa [queryResultSecond,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have he : Context Γ (equal 3 7) := Context.eqTrans (Context.conjunctionLeft h1)
    (Context.eqSymm (Context.conjunctionLeft h2))
  have he1 : Context Γ (graphFormula 6 4 5).encode := Context.conjunctionRight (Context.conjunctionRight h1)
  have he2 : Context Γ (graphFormula 6 8 9).encode := Context.conjunctionRight (Context.conjunctionRight h2)
  have ht : Context Γ (both (both (member 31 4) (member 40 5))
      (both (member 31 8) (member 40 9))) :=
    .mp he2 (.mp he1 (.mp hc (.closed two_edges_endpoints)))
  have hp : Context Γ rowPoints := by
    have h4 := Context.conjunctionLeft ht
    have h8 := Context.conjunctionRight ht
    exact Context.conjunctionIntro (Context.conjunctionLeft h4)
      (Context.conjunctionIntro (Context.conjunctionLeft h8)
        (Context.conjunctionIntro (Context.conjunctionRight h4)
          (Context.conjunctionIntro (Context.conjunctionRight h8)
            (Context.conjunctionIntro he1 he2))))
  exact .mp hp (.mp he (.mp ho (.closed same_row_order)))

theorem two_new_row_order_certificate : theoremCode (certificate two_new_row_order) =
    imp suffixOrder.encode (imp suffixClean.encode
      (imp queriedNewRow.encode (imp queriedNewRowSecond.encode
        (both forwardClause reverseClause)))) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationTwoNewRowOrder
#print axioms PASoundness.PAtoCompactMultiplicationTwoNewRowOrder.two_new_row_order
#print axioms PASoundness.PAtoCompactMultiplicationTwoNewRowOrder.two_new_row_order_certificate
