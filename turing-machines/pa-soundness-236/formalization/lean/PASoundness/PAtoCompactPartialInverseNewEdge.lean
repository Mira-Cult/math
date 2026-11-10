import PASoundness.PAtoCompactPointAdjoin
import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactAdjunction

/-! Local new-edge coverage from a supplied inverse-pair witness and a supplied
point-adjunction graph. Neither witness is constructed here; the no-spurious
edge direction, whole successor invariant and inverse existence remain open. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseNewEdge
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A supplied point-adjunction graph contains the adjoined point. -/
def adjoin_contains_point : KDerivation
    (imp (adjoinCode 7 11 9 14) (member 9 11)) := by
  let f := namedBoth (.imp (.member 9 14) (namedEither (.equal 14 11) (.member 7 14)))
    (.imp (namedEither (.equal 14 11) (.member 7 14)) (.member 9 14))
  have hi := universalInstance 14 11 f (by decide)
    (by simp [f, namedBoth, namedEither, Formula.binders])
    (by simp [f, namedBoth, namedEither, Formula.binders])
  have hi' : KDerivation (imp (adjoinCode 7 11 9 14)
      (both (imp (member 9 11) (either (equal 11 11) (member 7 11)))
        (imp (either (equal 11 11) (member 7 11)) (member 9 11)))) := by
    simpa [f, namedBoth, namedEither, adjoinCode, Formula.encode, replace, rename,
      both, neg, either] using hi
  apply Context.closeEmpty
  apply Context.deduction
  let A := adjoinCode 7 11 9 14
  have ha : Context [A] A := Context.head [] A
  have hp := Context.conjunctionRight (.mp ha (.closed hi'))
  have he : Context [A] (either (equal 11 11) (member 7 11)) :=
    Context.disjunctionLeft (.closed (equalityReflexive 11))
  exact .mp he hp

/-- A point at name 11, belonging to graph 9 and representing coordinates
(13,12), introduces the exact reverse-oriented graph edge. -/
def supplied_pair_introduces_edge : KDerivation
    (imp (both (member 9 11) (pairFormula 11 13 12).encode)
      (graphFormula 9 13 12).encode) := by
  let f : Formula := ((Formula.member 9 19).imp (pairFormula 19 13 12).not).not
  have hi := exists_variable_intro 19 11 f (by decide) (by decide) (by decide)
  have hf : (replace 19 11 f).encode =
      both (member 9 11) (pairFormula 11 13 12).encode := by
    have hf' : replace 19 11 f =
        ((Formula.member 9 11).imp (pairFormula 11 13 12).not).not := by decide
    rw [hf']
    rfl
  have hg : existsCode 19 f.encode = (graphFormula 9 13 12).encode := rfl
  rw [hf,hg] at hi
  exact hi

/-- Adjoining a represented pair (13,12) yields the corresponding new edge.
The pair and adjunction are explicit K antecedents. -/
def adjoin_new_inverse_edge : KDerivation
    (imp (adjoinCode 7 11 9 14)
      (imp (pairFormula 11 13 12).encode (graphFormula 9 13 12).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(pairFormula 11 13 12).encode,adjoinCode 7 11 9 14]
  have hp : Context Γ (pairFormula 11 13 12).encode := Context.head _ _
  have ha : Context Γ (adjoinCode 7 11 9 14) := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 9 11) := .mp ha (.closed adjoin_contains_point)
  exact .mp (Context.conjunctionIntro hm hp) (.closed supplied_pair_introduces_edge)

theorem adjoin_new_inverse_edge_certificate :
    theoremCode (certificate adjoin_new_inverse_edge) =
      imp (adjoinCode 7 11 9 14)
        (imp (pairFormula 11 13 12).encode (graphFormula 9 13 12).encode) :=
  certificate_correct adjoin_new_inverse_edge

end PASoundness.PAtoCompactPartialInverseNewEdge

#print axioms PASoundness.PAtoCompactPartialInverseNewEdge.adjoin_new_inverse_edge
#print axioms PASoundness.PAtoCompactPartialInverseNewEdge.adjoin_new_inverse_edge_certificate
