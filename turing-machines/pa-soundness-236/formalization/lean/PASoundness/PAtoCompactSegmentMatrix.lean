import PASoundness.PAtoCompactSegmentMatrixExists
import PASoundness.PAtoCompactSegmentForwardAll
import PASoundness.PAtoCompactSegmentOrderFromTransitive

/-! Combining arbitrary-initial-segment K proof clauses. The backward
bijection derivation remains explicit proof data until separately supplied. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSegmentMatrix
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactRestrictedMatrix
open PASoundness.PAtoCompactRestrictedOrderPoint PASoundness.PAtoCompactSegmentMatrixExists
open PASoundness.PAtoCompactSegmentForwardAll PASoundness.PAtoCompactSegmentOrderFromTransitive
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def backwardPremise : Nat := imp sourceTrans (imp targetTrans (imp sourceMember
  (imp targetMember (imp orderFormula.encode (imp filter (imp topEdge
    (imp bijectionFormula.encode backwardClause)))))))

/-- The actual forward and order clauses and the supplied backward proof
produce the exact shared-graph matrix. -/
def segment_matrix_of_backward (backward : KDerivation backwardPremise) :
    KDerivation (imp sourceTrans (imp targetTrans (imp sourceMember
      (imp targetMember (imp orderFormula.encode (imp filter (imp topEdge
        (imp bijectionFormula.encode restrictedMatrix)))))))) := by
  let Γ := [bijectionFormula.encode,topEdge,filter,orderFormula.encode,
    targetMember,sourceMember,targetTrans,sourceTrans]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hb : Context Γ bijectionFormula.encode := .head _ _
  have he : Context Γ topEdge := .hypothesis (by simp [Γ])
  have hf : Context Γ filter := .hypothesis (by simp [Γ])
  have ho : Context Γ orderFormula.encode := .hypothesis (by simp [Γ])
  have hm1 : Context Γ targetMember := .hypothesis (by simp [Γ])
  have hm0 : Context Γ sourceMember := .hypothesis (by simp [Γ])
  have ht1 : Context Γ targetTrans := .hypothesis (by simp [Γ])
  have ht0 : Context Γ sourceTrans := .hypothesis (by simp [Γ])
  have hforward : Context Γ forwardClause :=
    .mp hb (.mp he (.mp hf (.mp ho (.mp hm1 (.mp hm0 (.mp ht1 (.mp ht0
      (.closed segment_forward_all))))))))
  have hbackward : Context Γ backwardClause :=
    .mp hb (.mp he (.mp hf (.mp ho (.mp hm1 (.mp hm0 (.mp ht1 (.mp ht0
      (.closed backward))))))))
  have horder : Context Γ PASoundness.PAtoCompactRestrictedOrderAll.restrictedOrder :=
    .mp hf (.mp ho (.mp hm1 (.mp ht1 (.mp hm0 (.mp ht0
      (.closed segment_order_from_transitive))))))
  exact Context.conjunctionIntro (Context.conjunctionIntro hforward hbackward) horder

/-- The same explicit backward proof suffices for a prepared segment E after
constructing the endpoint filter and eliminating its witness. -/
def segment_target_of_backward (backward : KDerivation backwardPremise) :
    KDerivation (imp sourceTrans (imp targetTrans (imp sourceMember
      (imp targetMember (imp orderFormula.encode (imp topEdge
        (imp bijectionFormula.encode PASoundness.PAtoCompactRestrictedEquivalentTarget.endpointTarget.encode))))))) :=
  segment_target_of_matrix (segment_matrix_of_backward backward)

end PASoundness.PAtoCompactSegmentMatrix

#print axioms PASoundness.PAtoCompactSegmentMatrix.segment_target_of_backward
