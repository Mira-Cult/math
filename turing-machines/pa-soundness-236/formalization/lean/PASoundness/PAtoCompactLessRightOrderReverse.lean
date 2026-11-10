import PASoundness.PAtoCompactLessRightSegmentClosed
import PASoundness.PAtoCompactCandidateSymmetryObjectClosed

/-! The opposite equivalence orientation for the right-order substitution.
All candidate and transitivity guards remain explicit object-level premises. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLessRightOrderReverse
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactQuotientOrder
open PASoundness.PAtoCompactCandidateSymmetryObject PASoundness.PAtoCompactCandidateSymmetryObjectClosed
open PASoundness.PAtoCompactLessRightWrapper PASoundness.PAtoCompactLessRightSegmentClosed

/-- Under both candidate conditions and both outer transitivity conditions,
E(8,1) carries the original right-order relation from 1 to 8. -/
def right_order_substitutivity_reverse : KDerivation
    (imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp (candidateCode 8 37 32 33 34 30 35 10 36)
        (imp sourceTrans (imp targetTrans (imp equivalentEightOne.encode
          (imp lessFormula.encode targetLess.encode)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let D0 := candidateCode 0 37 32 33 34 30 35 10 36
  let D8 := candidateCode 8 37 32 33 34 30 35 10 36
  let Γ := [lessFormula.encode, equivalentEightOne.encode, targetTrans, sourceTrans, D8, D0]
  have h0 : Context Γ D0 := .hypothesis (by simp [Γ])
  have h8 : Context Γ D8 := .hypothesis (by simp [Γ])
  have hs : Context Γ sourceTrans := .hypothesis (by simp [Γ])
  have ht : Context Γ targetTrans := .hypothesis (by simp [Γ])
  have he : Context Γ equivalentEightOne.encode := .hypothesis (by simp [Γ])
  have hl : Context Γ lessFormula.encode := .head _ _
  have hf : Context Γ E18.encode := by
    have hr : Context Γ equivalentOneEight.encode := .mp he (.mp h8 (.closed symmetry_at_eight))
    have hsyntax : equivalentOneEight = E18 := by decide
    simpa only [hsyntax] using hr
  exact .mp hl (.mp hf (.mp ht (.mp hs (.mp h0 (.closed right_order_substitutivity)))))

theorem right_order_substitutivity_reverse_certificate :
    theoremCode (certificate right_order_substitutivity_reverse) =
      imp (candidateCode 0 37 32 33 34 30 35 10 36)
        (imp (candidateCode 8 37 32 33 34 30 35 10 36)
          (imp sourceTrans (imp targetTrans (imp equivalentEightOne.encode
            (imp lessFormula.encode targetLess.encode))))) :=
  certificate_correct right_order_substitutivity_reverse

end PASoundness.PAtoCompactLessRightOrderReverse

#print axioms PASoundness.PAtoCompactLessRightOrderReverse.right_order_substitutivity_reverse
#print axioms PASoundness.PAtoCompactLessRightOrderReverse.right_order_substitutivity_reverse_certificate
