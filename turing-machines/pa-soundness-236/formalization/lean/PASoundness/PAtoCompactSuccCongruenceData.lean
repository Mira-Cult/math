import PASoundness.PAtoCompactGraphRestriction
import PASoundness.PAtoCompactPointAdjoin
import PASoundness.PAtoCompactZeroSuccessor

/-! Fixed-name interfaces for a conditional successor-congruence argument.
These definitions assert no graph existence, quotient law, collection,
semantic soundness, or PA proof transport. Compact negation uses literal
code 1; no global irreflexivity of arbitrary K models is assumed. -/
namespace PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin

/-- Existing graph 6 contains only pair witnesses with source in 0 and target
in 1. The endpoint witnesses 25,26 and pair binders 20–22 are explicit. -/
def cleanGraph : Nat := allCode 19
  (imp (member 6 19) (edgePredicate 19 0 1).encode)

/-- Supplied old isomorphism matrix on input names 0,1 and graph name 6. -/
def oldMatrix : Nat := both bijectionFormula.encode orderFormula.encode

/-- Literal new bijection and order clauses on successor inputs 7,8 and
adjoined graph 9, without changing their internal binder labels. -/
def newBijection : CompactNamed.Formula :=
  CompactNamed.replace 6 9 (CompactNamed.replace 1 8 (CompactNamed.replace 0 7 bijectionFormula))

def newOrder : CompactNamed.Formula :=
  CompactNamed.replace 6 9 (CompactNamed.replace 1 8 (CompactNamed.replace 0 7 orderFormula))

def newMatrix : Nat := both newBijection.encode newOrder.encode

/-- Input self-membership is refuted relative to the literal compact code 1.
These are explicit hypotheses and do not claim falsehood of 1 in all models. -/
def sourceIrreflexive : Nat := neg (member 0 0)
def targetIrreflexive : Nat := neg (member 1 1)

def sourceSuccessor : Nat := successorCode 0 7 14
def targetSuccessor : Nat := successorCode 1 8 15
def newPair : Nat := (pairFormula 11 0 1).encode
def newGraph : Nat := adjoinCode 6 11 9 16

/-- The displayed substituted named clauses have only their intended free
names. This is syntactic and does not assert the quotient property. -/
theorem new_bijection_free : newBijection.free = {7,8,9} := by decide

theorem new_order_free : newOrder.free = {7,8,9} := by decide

end PASoundness.PAtoCompactSuccCongruenceData

#print axioms PASoundness.PAtoCompactSuccCongruenceData.new_bijection_free
#print axioms PASoundness.PAtoCompactSuccCongruenceData.new_order_free
