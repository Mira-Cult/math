import PASoundness.PAtoCompactCommonSourceSpanBase
import PASoundness.PAtoCompactCompositionAdjoinEdges
import PASoundness.PAtoCompactKuratowskiAnyNames

/-! One concrete graph-extension witness for common-source span collection.
Given image values at names 11 and 12 and old graph at 9, K constructs a pair
and a graph with that pair adjoined and its new edge present. This neither
establishes the full prefix invariant nor performs candidate induction. -/
namespace PASoundness.PAtoCompactCommonSourceSpanAppend

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactKuratowskiAnyNames PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactCompositionAdjoinEdges PASoundness.PAtoCompactAdjunction

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A selected pair at 16 and its membership in graph 17 introduce the
corresponding graph edge with the same witness. -/
def selected_pair_edge : KDerivation
    (imp (both (member 17 16) (pairFormula 16 11 12).encode)
      (graphFormula 17 11 12).encode) := by
  let f : Formula := ((Formula.member 17 19).imp (pairFormula 19 11 12).not).not
  have hi := exists_variable_intro 19 16 f (by decide) (by decide) (by decide)
  have hf : (replace 19 16 f).encode =
      both (member 17 16) (pairFormula 16 11 12).encode := by
    have hf' : replace 19 16 f =
        ((Formula.member 17 16).imp (pairFormula 16 11 12).not).not := by decide
    rw [hf']
    rfl
  have hg : existsCode 19 f.encode = (graphFormula 17 11 12).encode := rfl
  rw [hf,hg] at hi
  exact hi

/-- The same pair used by the supplied adjunction is an edge of the new
represented graph. -/
def selected_adjoined_edge : KDerivation
    (imp (adjoinCode 9 16 17 18)
      (imp (pairFormula 16 11 12).encode (graphFormula 17 11 12).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(pairFormula 16 11 12).encode, adjoinCode 9 16 17 18]
  have hp : Context Γ (pairFormula 16 11 12).encode := .head _ _
  have ha : Context Γ (adjoinCode 9 16 17 18) := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 17 16) := .mp ha (.closed adjoin_contains_point)
  exact .mp (Context.conjunctionIntro hm hp) (.closed selected_pair_edge)

/-- K constructs an ordered pair for the two selected images and a new graph
that adjoins it to graph 9, retaining the exact graph edge. Names 11 and 12
are syntactically different, but the represented images may coincide. -/
def span_pair_graph_exists : KDerivation
    (existsCode 16 (both (pairFormula 16 11 12).encode
      (existsCode 17 (both (adjoinCode 9 16 17 18)
        (graphFormula 17 11 12).encode)))) := by
  let P := (pairFormula 16 11 12).encode
  let A := adjoinCode 9 16 17 18
  let E := (graphFormula 17 11 12).encode
  have hpair : KDerivation (existsCode 16 P) :=
    pair_exists_with_names 11 12 16 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have hc := PASoundness.PAtoCompactPointAdjoinSelector.predicate_names_lt 9 16 23
  have h18c : 18 ≠ PASoundness.PAtoCompactPointAdjoinSelector.adjoinPredicate 9 16 23 := by omega
  have h17c : 17 ≠ PASoundness.PAtoCompactPointAdjoinSelector.adjoinPredicate 9 16 23 := by omega
  have hgraph : KDerivation (existsCode 17 A) :=
    adjoin_graph_exists_fresh 9 16 23 18 17 (by decide) (by decide)
      (by decide) (by decide) (by decide) h18c (by decide)
      (by decide) (by decide) (by decide) h17c
  have hunder : KDerivation (imp P (existsCode 17 (both A E))) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [P]
    have hp : Context Γ P := .head _ _
    have hpoint : Context Γ (imp A (both A E)) := by
      apply Context.deduction
      let Δ := [A,P]
      have ha : Context Δ A := .head _ _
      have hp' : Context Δ P := .hypothesis (by simp [Δ])
      have he : Context Δ E := .mp hp' (.mp ha (.closed selected_adjoined_edge))
      exact Context.conjunctionIntro ha he
    have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 17 h)) := by
      intro h hh
      have he : h = P := by simpa [Γ] using hh
      subst h
      exact (pairFormula 16 11 12).vacuity 17 (by decide)
    have hall := Context.generalize 17 hv hpoint
    exact exists_map_context hall (.closed hgraph)
  have hkeep : KDerivation (imp P (both P (existsCode 17 (both A E)))) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [P]
    have hp : Context Γ P := .head _ _
    exact Context.conjunctionIntro hp (.mp hp (.closed hunder))
  exact .mp hpair (existsCongr 16 hkeep)

theorem span_pair_graph_exists_certificate :
    theoremCode (certificate span_pair_graph_exists) =
      existsCode 16 (both (pairFormula 16 11 12).encode
        (existsCode 17 (both (adjoinCode 9 16 17 18)
          (graphFormula 17 11 12).encode))) :=
  certificate_correct span_pair_graph_exists

end PASoundness.PAtoCompactCommonSourceSpanAppend

#print axioms PASoundness.PAtoCompactCommonSourceSpanAppend.selected_pair_edge
#print axioms PASoundness.PAtoCompactCommonSourceSpanAppend.selected_adjoined_edge
#print axioms PASoundness.PAtoCompactCommonSourceSpanAppend.span_pair_graph_exists
#print axioms PASoundness.PAtoCompactCommonSourceSpanAppend.span_pair_graph_exists_certificate
