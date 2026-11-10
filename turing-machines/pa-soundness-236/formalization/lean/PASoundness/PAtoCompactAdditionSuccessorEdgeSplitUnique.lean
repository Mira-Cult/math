import PASoundness.PAtoCompactSuccCongruenceEdgeSplit

/-! Constructive K edge split for adjoining the top pair (31,32).
It assumes the pair and adjunction; it does not assert graph existence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorEdgeSplitUnique
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.PAtoCompactSuccCongruenceEdgeSplit
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def edgeSplitBody (a b u v : Nat) : Formula :=
  .imp (namedAdjoin 6 11 9 16) (.imp (pairFormula 11 a b)
    (.imp (graphFormula 9 u v)
      (namedEither (graphFormula 6 u v) (namedBoth (.equal u a) (.equal v b)))))

private def orig23 : KDerivation (edgeSplitBody 0 1 2 3).encode := by
  simpa [edgeSplitBody, conclusion, newGraph, newPair, namedAdjoin, namedEither, namedBoth,
    Formula.encode, adjoinCode, CompactProof.both, CompactProof.neg, CompactDerivations.either]
      using edge_split
private def orig45 : KDerivation (edgeSplitBody 0 1 4 5).encode := by
  simpa [edgeSplitBody, newGraph, newPair, namedAdjoin, namedEither, namedBoth,
    Formula.encode, adjoinCode, CompactProof.both, CompactProof.neg, CompactDerivations.either]
      using PASoundness.PAtoCompactSuccCongruenceEdgeSplit.edge_split_45
private def move23 : KDerivation (edgeSplitBody 31 1 2 3).encode := by
  have h := universalInstance 0 31 (edgeSplitBody 0 1 2 3) (by decide) (by decide) (by decide)
  have hc := KDerivation.mp (.generalize 0 orig23) h
  have hr : replace 0 31 (edgeSplitBody 0 1 2 3) = edgeSplitBody 31 1 2 3 := by decide
  rw [hr] at hc
  exact hc
private def move45 : KDerivation (edgeSplitBody 31 1 4 5).encode := by
  have h := universalInstance 0 31 (edgeSplitBody 0 1 4 5) (by decide) (by decide) (by decide)
  have hc := KDerivation.mp (.generalize 0 orig45) h
  have hr : replace 0 31 (edgeSplitBody 0 1 4 5) = edgeSplitBody 31 1 4 5 := by decide
  rw [hr] at hc
  exact hc
/-- An edge (2,3) of the supplied adjunction is old or has the new coordinates. -/
def edge_split_23 : KDerivation (imp (adjoinCode 6 11 9 16)
    (imp (pairFormula 11 31 32).encode (imp (graphFormula 9 2 3).encode
      (either (graphFormula 6 2 3).encode (both (equal 2 31) (equal 3 32)))))) := by
  have h := universalInstance 1 32 (edgeSplitBody 31 1 2 3) (by decide) (by decide) (by decide)
  have hc := KDerivation.mp (.generalize 1 move23) h
  have hr : replace 1 32 (edgeSplitBody 31 1 2 3) = edgeSplitBody 31 32 2 3 := by decide
  rw [hr] at hc
  simpa [edgeSplitBody, namedAdjoin, namedEither, namedBoth, Formula.encode,
    adjoinCode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using hc
/-- The corresponding split for the second edge (4,5). -/
def edge_split_45 : KDerivation (imp (adjoinCode 6 11 9 16)
    (imp (pairFormula 11 31 32).encode (imp (graphFormula 9 4 5).encode
      (either (graphFormula 6 4 5).encode (both (equal 4 31) (equal 5 32)))))) := by
  have h := universalInstance 1 32 (edgeSplitBody 31 1 4 5) (by decide) (by decide) (by decide)
  have hc := KDerivation.mp (.generalize 1 move45) h
  have hr : replace 1 32 (edgeSplitBody 31 1 4 5) = edgeSplitBody 31 32 4 5 := by decide
  rw [hr] at hc
  simpa [edgeSplitBody, namedAdjoin, namedEither, namedBoth, Formula.encode,
    adjoinCode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using hc

theorem edge_split_23_certificate : theoremCode (certificate edge_split_23) =
    imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode
      (imp (graphFormula 9 2 3).encode
        (either (graphFormula 6 2 3).encode (both (equal 2 31) (equal 3 32))))) :=
  certificate_correct edge_split_23
theorem edge_split_45_certificate : theoremCode (certificate edge_split_45) =
    imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode
      (imp (graphFormula 9 4 5).encode
        (either (graphFormula 6 4 5).encode (both (equal 4 31) (equal 5 32))))) :=
  certificate_correct edge_split_45
end PASoundness.PAtoCompactAdditionSuccessorEdgeSplitUnique
#print axioms PASoundness.PAtoCompactAdditionSuccessorEdgeSplitUnique.edge_split_23
#print axioms PASoundness.PAtoCompactAdditionSuccessorEdgeSplitUnique.edge_split_45
#print axioms PASoundness.PAtoCompactAdditionSuccessorEdgeSplitUnique.edge_split_23_certificate
#print axioms PASoundness.PAtoCompactAdditionSuccessorEdgeSplitUnique.edge_split_45_certificate
