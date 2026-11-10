import PASoundness.PAtoCompactCleanMatrixWitnessElim
import PASoundness.PAtoCompactSuccIsoAlpha

/-! Forward successor congruence for the proposed K order-isomorphism
relation, with supplied successor graphs and explicit source/target
transitivity. Old and new graph witnesses and the clean-filter, pair and
adjunction witnesses are constructed or eliminated by the proof. This is not
an arithmetic interpretation, full quotient equality, PA proof translation,
or an end-to-end PA soundness theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccessorCongruence
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.PAtoCompactSuccCongruenceMixedOrder PASoundness.PAtoCompactSuccCongruenceWitnessVacuity
open PASoundness.PAtoCompactCleanMatrixData PASoundness.PAtoCompactCleanMatrixWitnessElim
open PASoundness.PAtoCompactSuccIsoAlpha

/-- The precise target after removing the old graph witness. The source and
target successor graphs and the old-domain transitivity conditions remain
explicit premises. -/
def successorGoal : Formula := .imp (namedSuccessor 0 7 14)
  (.imp (namedSuccessor 1 8 15)
    (.imp (transitiveNamed 0) (.imp (transitiveNamed 1) targetEquivalent)))

/-- A supplied old graph with its isomorphism matrix yields the exact
successor goal; the internal filtered and new graph witnesses are eliminated. -/
def from_old_matrix : KDerivation (imp oldMatrix10.encode successorGoal.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [targetTrans,sourceTrans,targetSuccessor,sourceSuccessor,oldMatrix10.encode]
  have ho : Context Γ oldMatrix10.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ sourceSuccessor := .hypothesis (by simp [Γ])
  have ht : Context Γ targetSuccessor := .hypothesis (by simp [Γ])
  have hts : Context Γ sourceTrans := .hypothesis (by simp [Γ])
  have htt : Context Γ targetTrans := Context.head _ _
  have hex : Context Γ (existsCode 9 newMatrix) :=
    .mp htt (.mp hts (.mp ht (.mp hs (.mp ho (.closed filtered_successor_matrix)))))
  exact .mp hex (.closed new_graph_alpha)

/-- If two old inputs are related by the proposed order-isomorphism formula,
and their explicitly supplied successors and old-domain transitivity satisfy
the displayed graphs, then the successors are related by the same formula. -/
def successor_congruence : KDerivation (imp equivalentFormula.encode successorGoal.encode) := by
  have hv : KDerivation (imp successorGoal.encode (allCode 10 successorGoal.encode)) :=
    successorGoal.vacuity 10 (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [equivalentFormula.encode]
  have he : Context Γ equivalentFormula.encode := Context.head [] _
  have hex : Context Γ (existsCode 10 oldMatrix10.encode) := .mp he (.closed old_graph_alpha)
  exact Context.existsElim hv (.closed (.generalize 10 from_old_matrix)) hex

theorem successor_congruence_certificate : theoremCode (certificate successor_congruence) =
    imp equivalentFormula.encode successorGoal.encode := certificate_correct successor_congruence

end PASoundness.PAtoCompactSuccessorCongruence

#print axioms PASoundness.PAtoCompactSuccessorCongruence.successor_congruence
#print axioms PASoundness.PAtoCompactSuccessorCongruence.successor_congruence_certificate
