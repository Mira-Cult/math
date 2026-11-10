import PASoundness.PAtoCompactSuccCongruenceData
import PASoundness.PAtoCompactPartialInverseOldEdge

/-! Edge-coverage components of the supplied point-adjunction construction
for successor congruence. No graph construction, no-spurious direction,
bijection, order preservation, or quotient theorem is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccCongruenceEdgeCoverage
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactPartialInverseOldEdge
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Supplied new graph contains every entry of the supplied old graph. -/
def old_inclusion : KDerivation (imp newGraph
    (allCode 19 (imp (member 6 19) (member 9 19)))) := by
  let E := either (equal 16 11) (member 6 16)
  let B := both (imp (member 9 16) E) (imp E (member 9 16))
  have hp : KDerivation (imp B (imp (member 6 16) (member 9 16))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [member 6 16,B]
    have hm : Context Γ (member 6 16) := Context.head _ _
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    have he : Context Γ E := Context.disjunctionRight (a := equal 16 11) hm
    exact .mp he (Context.conjunctionRight hb)
  have hall : KDerivation (imp newGraph
      (allCode 16 (imp (member 6 16) (member 9 16)))) := allCongr 16 hp
  let f : Formula := .imp (.member 6 16) (.member 9 16)
  have ha := (universalAlpha 16 19 f (by decide) (by decide) (by decide)).1
  have ha' : KDerivation (imp (allCode 16 (imp (member 6 16) (member 9 16)))
      (allCode 19 (imp (member 6 19) (member 9 19)))) := by
    simpa [f, Formula.encode, replace, rename] using ha
  exact compose hall ha'

/-- Old graph edges survive the supplied point adjunction. -/
def old_edge : KDerivation (imp newGraph
    (imp (graphFormula 6 2 3).encode (graphFormula 9 2 3).encode)) :=
  compose old_inclusion (graph_edge_monotone 6 9 2 3)

/-- The supplied point-adjunction graph contains the designated pair object. -/
def contains_new_point : KDerivation (imp newGraph (member 9 11)) := by
  let f := namedBoth (.imp (.member 9 16) (namedEither (.equal 16 11) (.member 6 16)))
    (.imp (namedEither (.equal 16 11) (.member 6 16)) (.member 9 16))
  have hi := universalInstance 16 11 f (by decide)
    (by simp [f, namedBoth, namedEither, Formula.binders])
    (by simp [f, namedBoth, namedEither, Formula.binders])
  have hi' : KDerivation (imp newGraph
      (both (imp (member 9 11) (either (equal 11 11) (member 6 11)))
        (imp (either (equal 11 11) (member 6 11)) (member 9 11)))) := by
    simpa [f, newGraph, namedBoth, namedEither, adjoinCode, Formula.encode, replace, rename,
      both, neg, either] using hi
  apply Context.closeEmpty
  apply Context.deduction
  have ha : Context [newGraph] newGraph := Context.head [] newGraph
  have hp := Context.conjunctionRight (.mp ha (.closed hi'))
  have he : Context [newGraph] (either (equal 11 11) (member 6 11)) :=
    Context.disjunctionLeft (.closed (equalityReflexive 11))
  exact .mp he hp

/-- A designated pair witness in graph 9 supplies the corresponding edge. -/
def pair_introduces_edge : KDerivation
    (imp (both (member 9 11) newPair) (graphFormula 9 0 1).encode) := by
  let f : Formula := ((Formula.member 9 19).imp (pairFormula 19 0 1).not).not
  have hi := exists_variable_intro 19 11 f (by decide) (by decide) (by decide)
  have hf : (replace 19 11 f).encode = both (member 9 11) newPair := by
    have hf' : replace 19 11 f =
        ((Formula.member 9 11).imp (pairFormula 11 0 1).not).not := by decide
    rw [hf']
    rfl
  have hg : existsCode 19 f.encode = (graphFormula 9 0 1).encode := rfl
  rw [hf,hg] at hi
  exact hi

/-- The supplied pair and adjunction give the new endpoint edge. -/
def new_edge : KDerivation (imp newGraph
    (imp newPair (graphFormula 9 0 1).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [newPair,newGraph]
  have hp : Context Γ newPair := Context.head _ _
  have ha : Context Γ newGraph := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 9 11) := .mp ha (.closed contains_new_point)
  exact .mp (Context.conjunctionIntro hm hp) (.closed pair_introduces_edge)

theorem edge_coverage_certificate :
    theoremCode (certificate old_edge) = imp newGraph
      (imp (graphFormula 6 2 3).encode (graphFormula 9 2 3).encode) ∧
    theoremCode (certificate new_edge) = imp newGraph
      (imp newPair (graphFormula 9 0 1).encode) :=
  ⟨certificate_correct old_edge, certificate_correct new_edge⟩

end PASoundness.PAtoCompactSuccCongruenceEdgeCoverage

#print axioms PASoundness.PAtoCompactSuccCongruenceEdgeCoverage.old_edge
#print axioms PASoundness.PAtoCompactSuccCongruenceEdgeCoverage.new_edge
#print axioms PASoundness.PAtoCompactSuccCongruenceEdgeCoverage.edge_coverage_certificate
