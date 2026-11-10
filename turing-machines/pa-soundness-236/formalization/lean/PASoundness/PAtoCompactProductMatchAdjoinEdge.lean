import PASoundness.PAtoCompactProductMatchInsideAdjoinConditional
import PASoundness.PAtoCompactPartialInverseNewEdge

/-! The point adjoined for the selected product match is an actual graph
edge. Pair and adjunction witnesses remain explicit literal K antecedents. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchAdjoinEdge

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactAdjunction

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def contains_selected_pair : KDerivation
    (imp (adjoinCode 58 16 17 18) (member 17 16)) := by
  let f := namedBoth (.imp (.member 17 18) (namedEither (.equal 18 16) (.member 58 18)))
    (.imp (namedEither (.equal 18 16) (.member 58 18)) (.member 17 18))
  have hi := universalInstance 18 16 f (by decide) (by decide) (by decide)
  have hi' : KDerivation (imp (adjoinCode 58 16 17 18)
      (both (imp (member 17 16) (either (equal 16 16) (member 58 16)))
        (imp (either (equal 16 16) (member 58 16)) (member 17 16)))) := by
    simpa [f, adjoinCode, namedBoth, namedEither, Formula.encode, replace, rename,
      both, neg, either] using hi
  apply Context.closeEmpty
  apply Context.deduction
  have ha : Context [adjoinCode 58 16 17 18] (adjoinCode 58 16 17 18) := .head _ _
  have he : Context [adjoinCode 58 16 17 18] (either (equal 16 16) (member 58 16)) :=
    Context.disjunctionLeft (.closed (equalityReflexive 16))
  exact .mp he (Context.conjunctionRight (.mp ha (.closed hi')))

def pair_introduces_edge : KDerivation
    (imp (both (member 17 16) (pairFormula 16 74 35).encode)
      (graphFormula 17 74 35).encode) := by
  let f : Formula := ((Formula.member 17 19).imp (pairFormula 19 74 35).not).not
  have hi := exists_variable_intro 19 16 f (by decide) (by decide) (by decide)
  have hf : (replace 19 16 f).encode =
      both (member 17 16) (pairFormula 16 74 35).encode := by
    have h : replace 19 16 f =
        ((Formula.member 17 16).imp (pairFormula 16 74 35).not).not := by decide
    rw [h]
    rfl
  have hg : existsCode 19 f.encode = (graphFormula 17 74 35).encode := rfl
  rw [hf,hg] at hi
  exact hi

def selected_edge : KDerivation (imp (adjoinCode 58 16 17 18)
    (imp (pairFormula 16 74 35).encode (graphFormula 17 74 35).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(pairFormula 16 74 35).encode,adjoinCode 58 16 17 18]
  have hp : Context Γ (pairFormula 16 74 35).encode := .head _ _
  have ha : Context Γ (adjoinCode 58 16 17 18) := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 17 16) := .mp ha (.closed contains_selected_pair)
  exact .mp (Context.conjunctionIntro hm hp) (.closed pair_introduces_edge)

theorem selected_edge_certificate : theoremCode (certificate selected_edge) =
    imp (adjoinCode 58 16 17 18)
      (imp (pairFormula 16 74 35).encode (graphFormula 17 74 35).encode) := certificate_correct _

end PASoundness.PAtoCompactProductMatchAdjoinEdge

#print axioms PASoundness.PAtoCompactProductMatchAdjoinEdge.contains_selected_pair
#print axioms PASoundness.PAtoCompactProductMatchAdjoinEdge.pair_introduces_edge
#print axioms PASoundness.PAtoCompactProductMatchAdjoinEdge.selected_edge
#print axioms PASoundness.PAtoCompactProductMatchAdjoinEdge.selected_edge_certificate
