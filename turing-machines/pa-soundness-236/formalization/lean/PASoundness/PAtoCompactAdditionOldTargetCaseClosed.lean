import PASoundness.PAtoCompactAdditionOldTargetFromBijection
import PASoundness.PAtoCompactAdditionOldTargetInclusions
import PASoundness.PAtoCompactAdditionOldTargetSplitPremise
import PASoundness.PAtoCompactAdditionOldTargetSourceGuard

/-! The old-target witness case for the distinct-top addition graph. All
object-level graph, filter and old-bijection hypotheses remain explicit.
This is not full graph bijectivity, isomorphism, addition totality, or a PA
proof translation. No suffix transitivity is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionOldTargetCaseClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactAdditionSuccessorGraphClean
open PASoundness.PAtoCompactAdditionOldTargetUniform PASoundness.PAtoCompactAdditionOldTargetWitnessTransfer
open PASoundness.PAtoCompactAdditionOldTargetFromBijection PASoundness.PAtoCompactAdditionOldTargetInclusions
open PASoundness.PAtoCompactAdditionOldTargetSplitPremise PASoundness.PAtoCompactAdditionOldTargetSourceGuard
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- For each old target 28, the old matrix supplies a witness which remains
unique in the adjoined graph and whose source lies in the successor domain. -/
def old_target_case : KDerivation (imp suffix (imp oldMatrixAt.encode
    (imp oldClean.encode (imp (successorCode 31 38 39)
      (imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode
        (imp (member 34 28) (Formula.ex 2 newWitnessBody).encode))))))) := by
  let F := suffix
  let M := oldMatrixAt.encode
  let C := oldClean.encode
  let S := successorCode 31 38 39
  let A := adjoinCode 6 11 9 16
  let P := (pairFormula 11 31 32).encode
  let T := member 34 28
  let Γ := [T,P,A,S,C,M,F]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have ht : Context Γ T := .head _ _
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hm : Context Γ M := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hsplit : Context Γ splitUniform.encode := .mp hp (.mp ha (.closed split_from_graph_pair))
  have hguard : Context Γ sourceGuardUniform.encode := .mp hc (.closed source_guard_from_clean)
  have hsrc : Context Γ sourceInclusion.encode := .mp hs (.closed source_inclusion_from_successor)
  have hgraph : Context Γ graphInclusion.encode := .mp ha (.closed graph_inclusion_from_adjoin)
  have hold : Context Γ (Formula.ex 2 oldWitnessBody).encode := .mp ht (.mp hm (.closed old_target_from_matrix))
  exact .mp hold (.mp hgraph (.mp hsrc (.mp hguard (.mp hsplit
    (.mp ht (.mp hf (.closed old_target_witness_transfer)))))))

theorem old_target_case_certificate : theoremCode (certificate old_target_case) =
    imp suffix (imp oldMatrixAt.encode (imp oldClean.encode (imp (successorCode 31 38 39)
      (imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode
        (imp (member 34 28) (Formula.ex 2 newWitnessBody).encode)))))) :=
  certificate_correct old_target_case
end PASoundness.PAtoCompactAdditionOldTargetCaseClosed
#print axioms PASoundness.PAtoCompactAdditionOldTargetCaseClosed.old_target_case
#print axioms PASoundness.PAtoCompactAdditionOldTargetCaseClosed.old_target_case_certificate
