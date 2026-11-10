import PASoundness.PAtoCompactProductMatchProductLexPoint
import PASoundness.PAtoCompactProductMatchFactorOrderPoint
import PASoundness.PAtoCompactProductOutputReverseCoverage

/-! Fixed-point order comparisons needed for transported product lex order.
The source product matrix and output order clause remain explicit, and the
source/target output labels remain as displayed. No graph order is inferred. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputLexPoints

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactProductOutputReverseCoverage
open PASoundness.PAtoCompactProductMatchFactorOrderPoint

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceFrame : Formula := PAtoCompactProductMatchProductLexPoint.sourceFrame
def sourceLexPoint : Formula := replace 2 0 (replace 1 44 (replace 0 43
  PAtoCompactProductMatchProductLexPoint.sourcePoint))
def sourceTarget : Formula := .imp relocatedMatrix sourceLexPoint

theorem source_target_shape : replace 2 0 (replace 1 44 (replace 0 43 sourceFrame)) = sourceTarget := by decide

/-- Source product lex comparison, preserving factor order and source outputs
32 and 52. -/
def source_lex_point : KDerivation (imp relocatedMatrix.encode sourceLexPoint.encode) := by
  have h0 : KDerivation sourceFrame.encode := by
    simpa [sourceFrame, PAtoCompactProductMatchProductLexPoint.sourceFrame,
      CompactNamed.Formula.encode] using PAtoCompactProductMatchProductLexPoint.source_point
  have h1 := replace_derivation 0 43 sourceFrame (by decide) (by decide) h0
  have h2 := replace_derivation 1 44 (replace 0 43 sourceFrame) (by decide) (by decide) h1
  have h3 := replace_derivation 2 0 (replace 1 44 (replace 0 43 sourceFrame)) (by decide) (by decide) h2
  rw [source_target_shape] at h3
  simpa [sourceTarget, CompactNamed.Formula.encode] using h3

def imageFrame : Formula := PAtoCompactProductMatchFactorOrderPoint.firstFrame
def imageOrderPoint : Formula := replace 53 55 (replace 50 52 (replace 30 32
  PAtoCompactProductMatchFactorOrderPoint.firstPoint))
def imageTarget : Formula := .imp firstOrder imageOrderPoint

theorem image_target_shape : replace 53 55 (replace 50 52 (replace 30 32 imageFrame)) = imageTarget := by decide

/-- Output-isomorphism order comparison at source outputs 32,52 and their
images 33,55, conditional on the actual first-order clause. -/
def image_order_point : KDerivation (imp firstOrder.encode imageOrderPoint.encode) := by
  have h0 : KDerivation imageFrame.encode := by
    simpa [imageFrame, PAtoCompactProductMatchFactorOrderPoint.firstFrame,
      CompactNamed.Formula.encode] using first_order_point
  have h1 := replace_derivation 30 32 imageFrame (by decide) (by decide) h0
  have h2 := replace_derivation 50 52 (replace 30 32 imageFrame) (by decide) (by decide) h1
  have h3 := replace_derivation 53 55 (replace 50 52 (replace 30 32 imageFrame)) (by decide) (by decide) h2
  rw [image_target_shape] at h3
  simpa [imageTarget, CompactNamed.Formula.encode] using h3

theorem source_lex_point_certificate : theoremCode (certificate source_lex_point) =
    imp relocatedMatrix.encode sourceLexPoint.encode := certificate_correct _
theorem image_order_point_certificate : theoremCode (certificate image_order_point) =
    imp firstOrder.encode imageOrderPoint.encode := certificate_correct _

end PASoundness.PAtoCompactProductOutputLexPoints

#print axioms PASoundness.PAtoCompactProductOutputLexPoints.source_lex_point
#print axioms PASoundness.PAtoCompactProductOutputLexPoints.image_order_point
#print axioms PASoundness.PAtoCompactProductOutputLexPoints.source_lex_point_certificate
#print axioms PASoundness.PAtoCompactProductOutputLexPoints.image_order_point_certificate
