import PASoundness.PAtoCompactPartialInverseOldEdge
import PASoundness.PAtoCompactPartialInverseNewEdge

/-! Edge preservation and introduction for the fixed-name composition-graph
adjunction. The graph and pair witnesses are explicit K antecedents; no
witness existence, composition invariant or quotient result is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCompositionAdjoinEdges
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactTransitiveWitness PASoundness.PAtoCompactPartialInverseOldEdge
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The supplied point-adjunction contains each entry of the old graph. -/
def adjoin_old_entry : KDerivation
    (imp (adjoinCode 9 16 17 18) (allCode 19 (imp (member 9 19) (member 17 19)))) := by
  let E := either (equal 18 16) (member 9 18)
  let B := both (imp (member 17 18) E) (imp E (member 17 18))
  have hp : KDerivation (imp B (imp (member 9 18) (member 17 18))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [member 9 18,B]
    have hm : Context Γ (member 9 18) := Context.head _ _
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    have he : Context Γ E := Context.disjunctionRight (a := equal 18 16) hm
    exact .mp he (Context.conjunctionRight hb)
  have hall : KDerivation (imp (adjoinCode 9 16 17 18)
      (allCode 18 (imp (member 9 18) (member 17 18)))) := allCongr 18 hp
  let f : Formula := .imp (.member 9 18) (.member 17 18)
  have ha := (universalAlpha 18 19 f (by decide) (by decide) (by decide)).1
  have ha' : KDerivation (imp (allCode 18 (imp (member 9 18) (member 17 18)))
      (allCode 19 (imp (member 9 19) (member 17 19)))) := by
    simpa [f, Formula.encode, replace, rename] using ha
  exact compose hall ha'

/-- Every selected old composition edge remains after the supplied adjunction. -/
def adjoin_preserves_edge : KDerivation
    (imp (adjoinCode 9 16 17 18)
      (imp (graphFormula 9 2 3).encode (graphFormula 17 2 3).encode)) :=
  compose adjoin_old_entry (graph_edge_monotone 9 17 2 3)

/-- The supplied point-adjunction contains its adjoined pair object. -/
def adjoin_contains_point : KDerivation
    (imp (adjoinCode 9 16 17 18) (member 17 16)) := by
  let f := namedBoth (.imp (.member 17 18) (namedEither (.equal 18 16) (.member 9 18)))
    (.imp (namedEither (.equal 18 16) (.member 9 18)) (.member 17 18))
  have hi := universalInstance 18 16 f (by decide)
    (by simp [f, namedBoth, namedEither, Formula.binders])
    (by simp [f, namedBoth, namedEither, Formula.binders])
  have hi' : KDerivation (imp (adjoinCode 9 16 17 18)
      (both (imp (member 17 16) (either (equal 16 16) (member 9 16)))
        (imp (either (equal 16 16) (member 9 16)) (member 17 16)))) := by
    simpa [f, namedBoth, namedEither, adjoinCode, Formula.encode, replace, rename,
      both, neg, either] using hi
  apply Context.closeEmpty
  apply Context.deduction
  let A := adjoinCode 9 16 17 18
  have ha : Context [A] A := Context.head [] A
  have hp := Context.conjunctionRight (.mp ha (.closed hi'))
  have he : Context [A] (either (equal 16 16) (member 9 16)) :=
    Context.disjunctionLeft (.closed (equalityReflexive 16))
  exact .mp he hp

/-- The pair held at name 16 supplies the exact selected forward edge. -/
def selected_pair_introduces_edge : KDerivation
    (imp (both (member 17 16) (pairFormula 16 10 12).encode)
      (graphFormula 17 10 12).encode) := by
  let f : Formula := ((Formula.member 17 19).imp (pairFormula 19 10 12).not).not
  have hi := exists_variable_intro 19 16 f (by decide) (by decide) (by decide)
  have hf : (replace 19 16 f).encode =
      both (member 17 16) (pairFormula 16 10 12).encode := by
    have hf' : replace 19 16 f =
        ((Formula.member 17 16).imp (pairFormula 16 10 12).not).not := by decide
    rw [hf']
    rfl
  have hg : existsCode 19 f.encode = (graphFormula 17 10 12).encode := rfl
  rw [hf,hg] at hi
  exact hi

/-- The supplied pair and point-adjunction introduce the selected edge. -/
def adjoin_selected_edge : KDerivation
    (imp (adjoinCode 9 16 17 18)
      (imp (pairFormula 16 10 12).encode (graphFormula 17 10 12).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(pairFormula 16 10 12).encode,adjoinCode 9 16 17 18]
  have hp : Context Γ (pairFormula 16 10 12).encode := Context.head _ _
  have ha : Context Γ (adjoinCode 9 16 17 18) := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 17 16) := .mp ha (.closed adjoin_contains_point)
  exact .mp (Context.conjunctionIntro hm hp) (.closed selected_pair_introduces_edge)

theorem adjoin_preserves_edge_certificate : theoremCode (certificate adjoin_preserves_edge) =
    imp (adjoinCode 9 16 17 18)
      (imp (graphFormula 9 2 3).encode (graphFormula 17 2 3).encode) :=
  certificate_correct adjoin_preserves_edge

theorem adjoin_selected_edge_certificate : theoremCode (certificate adjoin_selected_edge) =
    imp (adjoinCode 9 16 17 18)
      (imp (pairFormula 16 10 12).encode (graphFormula 17 10 12).encode) :=
  certificate_correct adjoin_selected_edge

end PASoundness.PAtoCompactCompositionAdjoinEdges

#print axioms PASoundness.PAtoCompactCompositionAdjoinEdges.adjoin_preserves_edge
#print axioms PASoundness.PAtoCompactCompositionAdjoinEdges.adjoin_selected_edge
#print axioms PASoundness.PAtoCompactCompositionAdjoinEdges.adjoin_preserves_edge_certificate
#print axioms PASoundness.PAtoCompactCompositionAdjoinEdges.adjoin_selected_edge_certificate
