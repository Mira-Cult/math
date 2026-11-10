import PASoundness.PAtoCompactAdditionCombinedBijection
import PASoundness.PAtoCompactAdditionOrderAtNewDomains

/-! The literal isomorphism matrix for the proposed addition-successor graph.
The old isomorphism matrix, graph cleanliness, filter, source successor,
pair and both adjunctions remain explicit K antecedents. The needed
transitivity hypotheses are for the source and whole result, not the suffix.
No witness existence, addition totality, or PA soundness is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorIsoMatrix
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactAdditionCombinedBijection PASoundness.PAtoCompactAdditionOrderAtNewDomains
open PASoundness.PAtoCompactAdditionOldTargetFromBijection
attribute [local irreducible] imp Cantor.pair Cantor.triangle
private abbrev O := PASoundness.PAtoCompactAdditionSuccessorOldOld.oldOrder.encode
private abbrev C := PASoundness.PAtoCompactAdditionSuccessorGraphClean.oldClean.encode
private abbrev F := PASoundness.PAtoCompactAdditionSuccessorGraphClean.suffix
private abbrev S := PASoundness.PAtoCompactAdditionSuccessorGraphMixed.sourceTrans
private abbrev T := PASoundness.PAtoCompactAdditionSuccessorGraphMixed.targetTrans
private abbrev P := (pairFormula 11 31 32).encode
private abbrev A := adjoinCode 6 11 9 16
private abbrev Q := PASoundness.PAtoCompactAdditionRightContext.premises.encode
private abbrev D := suffixAdjoin
private def oldB := PASoundness.PAtoCompactAdditionOldSourceClosed.oldBijection
private theorem matrix_alignment : oldMatrixAt = namedBoth oldB
    PASoundness.PAtoCompactAdditionSuccessorOldOld.oldOrder := by decide
/-- The exact new bijection-and-order matrix on source 38, suffix 40, graph 9. -/
def newMatrixAt : Formula := namedBoth (replace 8 40 (replace 7 38 newBijection)) newOrderAt
/-- The given graph satisfies both clauses of the isomorphism matrix under the
explicit old-matrix, graph, filter, successor, and transitivity assumptions. -/
def isomorphism_matrix : KDerivation (imp Q (imp D (imp S (imp T newMatrixAt.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [T,S,D,Q]
  have hp : Context Γ Q := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .head _ _
  have hf : Context Γ F := Context.conjunctionLeft hp
  have hrest := Context.conjunctionRight hp
  have hm : Context Γ oldMatrixAt.encode := Context.conjunctionLeft hrest
  have hc : Context Γ C := Context.conjunctionLeft (Context.conjunctionRight hrest)
  have hrest2 := Context.conjunctionRight (Context.conjunctionRight hrest)
  have ha : Context Γ A := Context.conjunctionLeft (Context.conjunctionRight hrest2)
  have hpair : Context Γ P := Context.conjunctionRight (Context.conjunctionRight hrest2)
  have ho : Context Γ O := by
    rw [matrix_alignment] at hm
    exact Context.conjunctionRight hm
  have hb : Context Γ (replace 8 40 (replace 7 38 newBijection)).encode :=
    .mp hd (.mp hp (.closed combined_bijection))
  have horder : Context Γ newOrderAt.encode :=
    .mp ht (.mp hs (.mp hf (.mp hpair (.mp ha (.mp hc (.mp ho (.closed order_at_new_domains)))))))
  exact Context.conjunctionIntro hb horder

theorem isomorphism_matrix_certificate : theoremCode (certificate isomorphism_matrix) =
    imp Q (imp D (imp S (imp T newMatrixAt.encode))) :=
  certificate_correct isomorphism_matrix
end PASoundness.PAtoCompactAdditionSuccessorIsoMatrix
#print axioms PASoundness.PAtoCompactAdditionSuccessorIsoMatrix.isomorphism_matrix
#print axioms PASoundness.PAtoCompactAdditionSuccessorIsoMatrix.isomorphism_matrix_certificate
