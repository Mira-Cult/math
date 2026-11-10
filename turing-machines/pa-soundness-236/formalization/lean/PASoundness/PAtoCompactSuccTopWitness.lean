import PASoundness.PAtoCompactSuccCongruenceData
import PASoundness.PAtoCompactAdjunction

/-! Fixed-name top witnesses for conditional successor congruence in the
literal K calculus. Supplied successor, pair, and adjunction graphs remain
explicit antecedents; no graph existence, collection, or quotient theorem is
asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccTopWitness
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactSuccCongruenceData
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The target successor graph contains its old input. -/
def target_top_member : KDerivation (imp targetSuccessor (member 8 1)) :=
  successor_contains_input 1 8 15 (by decide) (by decide)

/-- The designated pair object belongs to the supplied adjoined graph. -/
def new_graph_contains_pair : KDerivation (imp newGraph (member 9 11)) := by
  let f : Formula := namedBoth
    (.imp (.member 9 16) (namedEither (.equal 16 11) (.member 6 16)))
    (.imp (namedEither (.equal 16 11) (.member 6 16)) (.member 9 16))
  have hi := CompactNamed.universalInstance 16 11 f (by decide)
    (by simp [f,namedBoth,namedEither,Formula.binders])
    (by simp [f,namedBoth,namedEither,Formula.binders])
  have hi' : KDerivation (imp newGraph
      (both (imp (member 9 11) (either (equal 11 11) (member 6 11)))
        (imp (either (equal 11 11) (member 6 11)) (member 9 11)))) := by
    simpa [f,newGraph,adjoinCode,namedBoth,namedEither,Formula.encode,
      CompactNamed.replace,CompactNamed.rename,CompactProof.both,CompactProof.neg,
      CompactDerivations.either] using hi
  apply Context.closeEmpty
  apply Context.deduction
  have hg : Context [newGraph] newGraph := Context.head [] _
  have hpoint := Context.mp hg (.closed hi')
  have heq : Context [newGraph] (equal 11 11) := .closed (equalityReflexive 11)
  exact .mp (Context.disjunctionLeft (b := member 6 11) heq) (Context.conjunctionRight hpoint)

/-- Supplied graph membership and the supplied pair provide the exact edge.
Witness 11 is introduced into graphFormula's bound name 19 capture-safely. -/
def graph_from_pair : KDerivation
    (imp (both (member 9 11) newPair) (graphFormula 9 0 1).encode) := by
  let f : Formula := namedBoth (.member 9 19) (pairFormula 19 0 1)
  have hi := exists_variable_intro 19 11 f (by decide) (by decide) (by decide)
  have hreplace : CompactNamed.replace 19 11 f =
      namedBoth (.member 9 11) (pairFormula 11 0 1) := by decide
  rw [hreplace] at hi
  change KDerivation (imp (both (member 9 11) newPair) (graphFormula 9 0 1).encode) at hi
  exact hi

/-- Given the designated pair and exact adjunction, the new graph contains the
new top edge. -/
def new_top_edge : KDerivation (imp newGraph (imp newPair (graphFormula 9 0 1).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [newPair,newGraph]
  have hp : Context Γ newPair := Context.head _ _
  have hg : Context Γ newGraph := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 9 11) := .mp hg (.closed new_graph_contains_pair)
  exact .mp (Context.conjunctionIntro hm hp) (.closed graph_from_pair)

theorem top_witness_certificates :
    theoremCode (certificate target_top_member) = imp targetSuccessor (member 8 1) ∧
    theoremCode (certificate new_top_edge) =
      imp newGraph (imp newPair (graphFormula 9 0 1).encode) :=
  ⟨certificate_correct target_top_member, certificate_correct new_top_edge⟩

end PASoundness.PAtoCompactSuccTopWitness

#print axioms PASoundness.PAtoCompactSuccTopWitness.target_top_member
#print axioms PASoundness.PAtoCompactSuccTopWitness.new_graph_contains_pair
#print axioms PASoundness.PAtoCompactSuccTopWitness.graph_from_pair
#print axioms PASoundness.PAtoCompactSuccTopWitness.new_top_edge
#print axioms PASoundness.PAtoCompactSuccTopWitness.top_witness_certificates
