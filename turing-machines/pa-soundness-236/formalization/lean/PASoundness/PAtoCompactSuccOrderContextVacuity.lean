import PASoundness.PAtoCompactSuccCongruenceOrderAlpha
import PASoundness.PAtoCompactSuccCongruenceMixedOrder
import PASoundness.PAtoCompactSuccCongruenceData

/-! Literal K vacuity at the four pointwise order names for an explicit
six-hypothesis context. These are proof-data side conditions, not a proof of
the order cases, graph existence, or successor congruence. Compact negation
uses code 1; no global irreflexivity assumption is introduced. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccOrderContextVacuity
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactSuccCongruenceOrderAlpha PASoundness.PAtoCompactSuccCongruenceMixedOrder
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactPointAdjoin
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Context order matches the six curried successor-order hypotheses. -/
def orderContext : List Nat :=
  [targetTrans,sourceTrans,newPair,newGraph,cleanGraph,oldOrderFresh.encode]

def cleanFormula : Formula := .all 19 (.imp (.member 6 19) (edgePredicate 19 0 1))

def transFormula (a : Nat) : Formula := .all 37 (.all 38
  (.imp (.member a 37) (.imp (.member 37 38) (.member a 38))))

/-- Each of the four point names is absent from every fixed named hypothesis,
including all displayed graph, pair and quantifier binder names. -/
theorem old_order_absent : ∀ x ∈ [2,4,3,5], x ∉ oldOrderFresh.names := by decide

theorem clean_absent : ∀ x ∈ [2,4,3,5], x ∉ cleanFormula.names := by decide

theorem graph_absent : ∀ x ∈ [2,4,3,5], x ∉ (namedAdjoin 6 11 9 16).names := by decide

theorem pair_absent : ∀ x ∈ [2,4,3,5], x ∉ (pairFormula 11 0 1).names := by decide

theorem source_absent : ∀ x ∈ [2,4,3,5], x ∉ (transFormula 0).names := by decide

theorem target_absent : ∀ x ∈ [2,4,3,5], x ∉ (transFormula 1).names := by decide

/-- Explicit K vacuity for every member of the displayed fixed context at any
of the four order names. The order and contents of the context are literal. -/
def context_vacuity (x : Nat) (hx : x ∈ [2,4,3,5]) :
    ∀ h, h ∈ orderContext → KDerivation (imp h (allCode x h)) := by
  intro h hh
  simp only [orderContext, List.mem_cons, List.not_mem_nil, or_false] at hh
  by_cases ht : h = targetTrans
  · subst h
    have hv := (transFormula 1).vacuity x (target_absent x hx)
    simpa [transFormula, targetTrans, PASoundness.PAtoCompactTransitiveSuccessor.transitiveCode,
      Formula.encode] using hv
  by_cases hs : h = sourceTrans
  · subst h
    have hv := (transFormula 0).vacuity x (source_absent x hx)
    simpa [transFormula, sourceTrans, PASoundness.PAtoCompactTransitiveSuccessor.transitiveCode,
      Formula.encode] using hv
  by_cases hp : h = newPair
  · subst h
    simpa [newPair] using (pairFormula 11 0 1).vacuity x (pair_absent x hx)
  by_cases hg : h = newGraph
  · subst h
    have hv := (namedAdjoin 6 11 9 16).vacuity x (graph_absent x hx)
    simpa [newGraph, namedAdjoin, adjoinCode, namedBoth, namedEither, Formula.encode,
      CompactProof.both, CompactProof.neg, CompactDerivations.either] using hv
  by_cases hc : h = cleanGraph
  · subst h
    have hv := cleanFormula.vacuity x (clean_absent x hx)
    simpa [cleanFormula, cleanGraph, Formula.encode] using hv
  have ho : h = oldOrderFresh.encode := by
    simpa [ht,hs,hp,hg,hc] using hh
  subst h
  exact oldOrderFresh.vacuity x (old_order_absent x hx)

end PASoundness.PAtoCompactSuccOrderContextVacuity

#print axioms PASoundness.PAtoCompactSuccOrderContextVacuity.context_vacuity
