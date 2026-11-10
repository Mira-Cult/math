import PASoundness.PAtoCompactSegmentMatrix
import PASoundness.PAtoCompactSegmentBackwardFinal

/-! The actual arbitrary-initial-segment matrix and prepared E endpoint.
The original isomorphism clauses, endpoint graph and domain hypotheses remain
explicit; no old graph existential or quotient-order theorem is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSegmentMatrixClosed
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSegmentMatrixExists
open PASoundness.PAtoCompactRestrictedMatrix PASoundness.PAtoCompactRestrictedOrderPoint
open PASoundness.PAtoCompactSegmentMatrix PASoundness.PAtoCompactSegmentBackwardFinal
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def backward_reordered : KDerivation backwardPremise := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [bijectionFormula.encode,topEdge,filter,orderFormula.encode,
    targetMember,sourceMember,targetTrans,sourceTrans]
  have hb : Context Γ bijectionFormula.encode := .head _ _
  have he : Context Γ topEdge := .hypothesis (by simp [Γ])
  have hf : Context Γ filter := .hypothesis (by simp [Γ])
  have ho : Context Γ orderFormula.encode := .hypothesis (by simp [Γ])
  have hm1 : Context Γ targetMember := .hypothesis (by simp [Γ])
  have hm0 : Context Γ sourceMember := .hypothesis (by simp [Γ])
  have ht1 : Context Γ targetTrans := .hypothesis (by simp [Γ])
  have ht0 : Context Γ sourceTrans := .hypothesis (by simp [Γ])
  exact .mp he (.mp hf (.mp hb (.mp ho (.mp hm1 (.mp hm0 (.mp ht1 (.mp ht0
    (.closed backward_all))))))))

/-- From a supplied original isomorphism and one selected matched pair,
K constructs an isomorphism of their represented initial segments. -/
def segment_target : KDerivation (imp sourceTrans (imp targetTrans (imp sourceMember
      (imp targetMember (imp orderFormula.encode (imp topEdge
        (imp bijectionFormula.encode PASoundness.PAtoCompactRestrictedEquivalentTarget.endpointTarget.encode))))))) :=
  segment_target_of_backward backward_reordered

theorem segment_target_certificate : theoremCode (certificate segment_target) =
    imp sourceTrans (imp targetTrans (imp sourceMember
      (imp targetMember (imp orderFormula.encode (imp topEdge
        (imp bijectionFormula.encode PASoundness.PAtoCompactRestrictedEquivalentTarget.endpointTarget.encode)))))) :=
  certificate_correct segment_target

end PASoundness.PAtoCompactSegmentMatrixClosed

#print axioms PASoundness.PAtoCompactSegmentMatrixClosed.segment_target
