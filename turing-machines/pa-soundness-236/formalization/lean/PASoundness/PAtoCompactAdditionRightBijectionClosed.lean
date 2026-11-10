import PASoundness.PAtoCompactAdditionRightBijectionCases
import PASoundness.PAtoCompactAdditionRightContext
import PASoundness.PAtoCompactAdditionOldTargetCaseClosed
import PASoundness.PAtoCompactAdditionTopTargetTransport

/-! Assemble the exact right-bijection clause for the distinct-top addition
extension from proved old and new target cases. The source successor, old
matrix and graph, suffix filter, graph pair and adjunctions remain explicit K
antecedents. This does not prove the left bijection clause, graph isomorphism,
addition totality, or the PA bridge. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionRightBijectionClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactAdditionSuccessorGraphClean
open PASoundness.PAtoCompactAdditionOldTargetFromBijection PASoundness.PAtoCompactAdditionOldTargetWitnessTransfer
open PASoundness.PAtoCompactAdditionOldTargetCaseClosed PASoundness.PAtoCompactAdditionTopTargetTransport
open PASoundness.PAtoCompactAdditionRightBijectionCases PASoundness.PAtoCompactAdditionRightContext
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def old_case : KDerivation (imp premises.encode
    (imp (member 34 28) (rightBody 28).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 34 28,premises.encode]
  have ht : Context Γ (member 34 28) := .head _ _
  have hP : Context Γ premises.encode := .hypothesis (by simp [Γ])
  have hF : Context Γ suffix := Context.conjunctionLeft hP
  have hM : Context Γ oldMatrixAt.encode := Context.conjunctionLeft (Context.conjunctionRight hP)
  have hC : Context Γ oldClean.encode := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hP))
  have hS : Context Γ (successorCode 31 38 39) :=
    Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hP)))
  have hA : Context Γ (adjoinCode 6 11 9 16) :=
    Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hP))))
  have hQ : Context Γ (pairFormula 11 31 32).encode :=
    Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hP))))
  have hw : Context Γ (Formula.ex 2 newWitnessBody).encode :=
    .mp ht (.mp hQ (.mp hA (.mp hS (.mp hC (.mp hM (.mp hF (.closed old_target_case)))))))
  simpa only [old_witness_alignment] using hw

private def top_case : KDerivation (imp premises.encode
    (imp (equal 28 32) (rightBody 28).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal 28 32,premises.encode]
  have ht : Context Γ (equal 28 32) := .head _ _
  have hP : Context Γ premises.encode := .hypothesis (by simp [Γ])
  have hF : Context Γ suffix := Context.conjunctionLeft hP
  have hC : Context Γ oldClean.encode := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hP))
  have hS : Context Γ (successorCode 31 38 39) :=
    Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hP)))
  have hA : Context Γ (adjoinCode 6 11 9 16) :=
    Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hP))))
  have hQ : Context Γ (pairFormula 11 31 32).encode :=
    Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hP))))
  have hw : Context Γ (Formula.ex 2 newWitnessBody).encode :=
    .mp ht (.mp hC (.mp hQ (.mp hA (.mp hS (.mp hF (.closed top_target_case))))))
  simpa only [old_witness_alignment] using hw

/-- The supplied finite graph extension has the exact right-bijection clause. -/
def right_bijection_closed : KDerivation (imp premises.encode
    (imp (adjoinCode 34 32 40 41) rightClause.encode)) :=
  right_from_cases premises.encode premises_vacuity old_case top_case

theorem right_bijection_closed_certificate : theoremCode (certificate right_bijection_closed) =
    imp premises.encode (imp (adjoinCode 34 32 40 41) rightClause.encode) :=
  certificate_correct right_bijection_closed
end PASoundness.PAtoCompactAdditionRightBijectionClosed
#print axioms PASoundness.PAtoCompactAdditionRightBijectionClosed.right_bijection_closed
#print axioms PASoundness.PAtoCompactAdditionRightBijectionClosed.right_bijection_closed_certificate
