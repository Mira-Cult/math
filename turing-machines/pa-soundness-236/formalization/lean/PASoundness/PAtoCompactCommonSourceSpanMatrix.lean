import PASoundness.PAtoCompactCommonSourceSpanInputMatrices
import PASoundness.PAtoCompactCommonSourceSpanInverseRestriction
import PASoundness.PAtoCompactCommonSourceSpanComposition
import PASoundness.PAtoCompactRestrictedSymmetry
import PASoundness.PAtoCompactConditionalTransitivityBijection
import PASoundness.PAtoCompactConditionalTransitivityMatrix
import PASoundness.PAtoCompactScopedActiveReplace

/-! Assemble the target isomorphism matrix from the supplied common-source
span graph, the actual two input isomorphism matrices, and the supplied
restricted inverse matrix for the first input. The three graph witnesses
remain explicit; no endpoint-candidate condition is imposed and no graph
existence is claimed here. -/
namespace PASoundness.PAtoCompactCommonSourceSpanMatrix

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactIsoConditionalWrapper PASoundness.PAtoCompactRestrictedInverseFirst
open PASoundness.PAtoCompactCommonSourceSpanInputMatrices
open PASoundness.PAtoCompactCommonSourceSpanInverseRestriction PASoundness.PAtoCompactCommonSourceSpanInversePath
open PASoundness.PAtoCompactCommonSourceSpanComposition PASoundness.PAtoCompactScopedActiveReplace

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def baseFrame : Formula := .imp forwardMatrix (.imp restrictedInverseMatrix reverseMatrix7)
private def movedGraph : Formula := replace 6 14 baseFrame
private def movedSource : Formula := replace 0 25 movedGraph
private def movedTarget : Formula := replace 1 0 movedSource
private def swapped : Formula := replace 25 1 movedTarget
private def finalFrame : Formula := replace 7 6 swapped

def firstMatrix14 : Formula := replace 6 14 firstMatrix

private theorem base_frame_code : baseFrame.encode =
    imp forwardMatrix.encode (imp restrictedInverseMatrix.encode reverseMatrix7.encode) := rfl

private theorem final_frame_alignment : finalFrame =
    .imp firstMatrix14 (.imp renamedRestriction PASoundness.PAtoCompactConditionalTransitivityMatrix.sourceMatrix) := by decide

/-- The original first isomorphism and its supplied restricted inverse imply
the exact reverse isomorphism matrix on graph 6. -/
def inverse_matrix : KDerivation (imp firstMatrix14.encode
    (imp renamedRestriction.encode PASoundness.PAtoCompactConditionalTransitivityMatrix.sourceMatrix.encode)) := by
  have hbase : KDerivation baseFrame.encode := by
    rw [base_frame_code]
    exact PASoundness.PAtoCompactRestrictedSymmetry.matrix_step
  have h0 := replace_derivation 6 14 baseFrame (by decide) (by decide) hbase
  have h1 := replace_derivation 0 25 movedGraph (by decide) (by decide) (by simpa only [movedGraph] using h0)
  have h2 := replace_derivation 1 0 movedSource (by decide) (by decide) (by simpa only [movedSource] using h1)
  have h3 := replace_derivation 25 1 movedTarget (by decide) (by decide) (by simpa only [movedTarget] using h2)
  have h4 := replace_derivation 7 6 swapped (by decide) (by decide) (by simpa only [swapped] using h3)
  have hfinal : KDerivation finalFrame.encode := by simpa only [finalFrame] using h4
  rw [final_frame_alignment] at hfinal
  exact hfinal

private theorem second_matrix_alignment :
    secondMatrix = PASoundness.PAtoCompactConditionalTransitivityMatrix.secondMatrix := by decide

/-- Supplied input matrices, inverse correspondence matrix and span graph
yield the exact isomorphism matrix for graph 9 from first image 0 to second
image 8. Both bijection and order follow from existing matrix transfers. -/
def span_isomorphism_matrix : KDerivation
    (imp firstMatrix14.encode (imp secondMatrix.encode
      (imp renamedRestriction.encode (imp spanFull.encode
        PASoundness.PAtoCompactConditionalTransitivityMatrix.targetMatrix.encode)))) := by
  have htransfer := PASoundness.PAtoCompactConditionalTransitivityMatrix.matrix_of_bijection
    PASoundness.PAtoCompactConditionalTransitivityBijection.bijection_transfer
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [spanFull.encode,renamedRestriction.encode,secondMatrix.encode,firstMatrix14.encode]
  have hspan : Context Γ spanFull.encode := .head _ _
  have hinv : Context Γ renamedRestriction.encode := .hypothesis (by simp [Γ])
  have hsecond : Context Γ secondMatrix.encode := .hypothesis (by simp [Γ])
  have hfirst : Context Γ firstMatrix14.encode := .hypothesis (by simp [Γ])
  have hsource : Context Γ PASoundness.PAtoCompactConditionalTransitivityMatrix.sourceMatrix.encode :=
    .mp hinv (.mp hfirst (.closed inverse_matrix))
  have hsecond' : Context Γ PASoundness.PAtoCompactConditionalTransitivityMatrix.secondMatrix.encode := by
    simpa only [second_matrix_alignment] using hsecond
  have hcorr : Context Γ inverseCorrespondence.encode :=
    .mp hinv (.closed restricted_inverse_correspondence)
  have hcomposition : Context Γ PASoundness.PAtoCompactConditionalTransitivityPoint.composition.encode :=
    .mp hspan (.mp hcorr (.closed span_to_composition))
  exact .mp hcomposition (.mp hsecond' (.mp hsource (.closed htransfer)))

theorem span_isomorphism_matrix_certificate : theoremCode (certificate span_isomorphism_matrix) =
    imp firstMatrix14.encode (imp secondMatrix.encode
      (imp renamedRestriction.encode (imp spanFull.encode
        PASoundness.PAtoCompactConditionalTransitivityMatrix.targetMatrix.encode))) :=
  certificate_correct span_isomorphism_matrix

end PASoundness.PAtoCompactCommonSourceSpanMatrix

#print axioms PASoundness.PAtoCompactCommonSourceSpanMatrix.firstMatrix14
#print axioms PASoundness.PAtoCompactCommonSourceSpanMatrix.inverse_matrix
#print axioms PASoundness.PAtoCompactCommonSourceSpanMatrix.span_isomorphism_matrix
#print axioms PASoundness.PAtoCompactCommonSourceSpanMatrix.span_isomorphism_matrix_certificate
