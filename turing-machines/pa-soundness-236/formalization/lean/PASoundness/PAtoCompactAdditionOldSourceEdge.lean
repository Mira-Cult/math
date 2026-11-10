import PASoundness.PAtoCompactAdditionSuccessorEdgeSplitUnique
import PASoundness.PAtoCompactTransitiveClosure

/-! An old-source edge of the extended graph already belonged to the old
graph. The pair and graph adjunction are supplied. This pointwise reduction
neither asserts functionality nor a complete bijection. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionOldSourceEdge
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactAdditionSuccessorEdgeSplitUnique
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def base : KDerivation (edgeSplitBody 31 32 2 3).encode := by
  simpa [edgeSplitBody, namedAdjoin, namedEither, namedBoth, Formula.encode,
    adjoinCode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using edge_split_23
/-- Split the new edge at source 2 and target 4. -/
def edge_split_24 : KDerivation (imp (adjoinCode 6 11 9 16)
    (imp (pairFormula 11 31 32).encode (imp (graphFormula 9 2 4).encode
      (either (graphFormula 6 2 4).encode (both (equal 2 31) (equal 4 32)))))) := by
  have h := universalInstance 3 4 (edgeSplitBody 31 32 2 3) (by decide) (by decide) (by decide)
  have hc := KDerivation.mp (.generalize 3 base) h
  have hr : replace 3 4 (edgeSplitBody 31 32 2 3) = edgeSplitBody 31 32 2 4 := by decide
  rw [hr] at hc
  simpa [edgeSplitBody, namedAdjoin, namedEither, namedBoth, Formula.encode,
    adjoinCode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using hc

/-- Any edge of the adjoined graph starting at an old source is an old edge.
No cleanliness, domain transitivity, or suffix hypotheses are required. -/
def old_source_edge : KDerivation (imp (adjoinCode 6 11 9 16)
    (imp (pairFormula 11 31 32).encode (imp (member 31 2)
      (imp (graphFormula 9 2 4).encode (graphFormula 6 2 4).encode)))) := by
  let A := adjoinCode 6 11 9 16
  let P := (pairFormula 11 31 32).encode
  let M := member 31 2
  let G := (graphFormula 9 2 4).encode
  let O := (graphFormula 6 2 4).encode
  let T := both (equal 2 31) (equal 4 32)
  let Γ := [G,M,P,A]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hm : Context Γ M := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .head _ _
  have hs : Context Γ (either O T) := .mp hg (.mp hp (.mp ha (.closed edge_split_24)))
  apply Context.disjunctionElim hs
  · exact Context.head Γ O
  · let Δ := T :: Γ
    have ht : Context Δ T := .head _ _
    have he : Context Δ (equal 2 31) := Context.conjunctionLeft ht
    have hm' : Context Δ (member 31 2) := .under hm T
    have hself : Context Δ (member 31 31) :=
      .mp he (.mp hm' (.closed (memberRightEquality 31 2 31)))
    have hfalse : Context Δ 1 := .mp hself (.closed (self_membership_implies_code_one 31))
    exact Context.explode O hfalse

theorem old_source_edge_certificate : theoremCode (certificate old_source_edge) =
    imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode (imp (member 31 2)
      (imp (graphFormula 9 2 4).encode (graphFormula 6 2 4).encode))) :=
  certificate_correct old_source_edge
end PASoundness.PAtoCompactAdditionOldSourceEdge
#print axioms PASoundness.PAtoCompactAdditionOldSourceEdge.old_source_edge
#print axioms PASoundness.PAtoCompactAdditionOldSourceEdge.old_source_edge_certificate
