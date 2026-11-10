import PASoundness.PAtoCompactCleanMatrix
import PASoundness.PAtoCompactCleanFilterExists
import PASoundness.PAtoCompactSuccCongruenceWitnessElim

/-! Eliminate the clean old-graph witness from the conditional successor
matrix construction, using the actual K endpoint-filter existence theorem.
The original graph's old matrix, both successor graphs and old-domain
transitivity remain explicit antecedents. This does not yet eliminate the
original graph witness or prove quotient congruence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCleanMatrixWitnessElim
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccCongruenceMixedOrder
open PASoundness.PAtoCompactSuccCongruenceWitnessVacuity PASoundness.PAtoCompactSuccCongruenceWitnessElim
open PASoundness.PAtoCompactCleanMatrixData PASoundness.PAtoCompactCleanMatrix
open PASoundness.PAtoCompactCleanFilterExists

/-- Exact successor matrix goal over original graph10, with output graph9
existentially bound. The clean filter graph name6 does not occur. -/
def goalNamed : Formula := .imp oldMatrix10
  (.imp (namedSuccessor 0 7 14) (.imp (namedSuccessor 1 8 15)
    (.imp (transitiveNamed 0) (.imp (transitiveNamed 1) (.ex 9 newMatrixNamed)))))

/-- A supplied filter gives the exact desired implication. -/
def from_filter : KDerivation (imp filterCode goalNamed.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [targetTrans,sourceTrans,targetSuccessor,sourceSuccessor,oldMatrix10.encode,filterCode]
  have hf : Context Γ filterCode := .hypothesis (by simp [Γ])
  have ho : Context Γ oldMatrix10.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ sourceSuccessor := .hypothesis (by simp [Γ])
  have ht : Context Γ targetSuccessor := .hypothesis (by simp [Γ])
  have hts : Context Γ sourceTrans := .hypothesis (by simp [Γ])
  have htt : Context Γ targetTrans := Context.head _ _
  have hmc : Context Γ (both oldMatrix cleanGraph) := .mp ho (.mp hf (.closed clean_matrix))
  have hm := Context.conjunctionLeft hmc
  have hc := Context.conjunctionRight hmc
  have hr : Context Γ retainedCode := Context.conjunctionIntro hm (Context.conjunctionIntro hc
    (Context.conjunctionIntro hs (Context.conjunctionIntro ht (Context.conjunctionIntro hts htt))))
  exact .mp hr (.closed successor_graph_exists)

/-- K constructs the clean filtered graph internally and eliminates its name;
all remaining assumptions are shown explicitly in the named goal. -/
def filtered_successor_matrix : KDerivation goalNamed.encode := by
  have hv : KDerivation (imp goalNamed.encode (allCode 6 goalNamed.encode)) :=
    goalNamed.vacuity 6 (by decide)
  apply Context.closeEmpty
  exact Context.existsElim hv (.closed (.generalize 6 from_filter)) (.closed clean_filter_exists)

theorem filtered_successor_matrix_certificate :
    theoremCode (certificate filtered_successor_matrix) = goalNamed.encode :=
  certificate_correct filtered_successor_matrix

end PASoundness.PAtoCompactCleanMatrixWitnessElim

#print axioms PASoundness.PAtoCompactCleanMatrixWitnessElim.filtered_successor_matrix
#print axioms PASoundness.PAtoCompactCleanMatrixWitnessElim.filtered_successor_matrix_certificate
