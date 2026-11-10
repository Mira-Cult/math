import PASoundness.PAtoCompactProductMatchFactorEquality
import PASoundness.PAtoCompactProductOutputImagePoint

/-! Two source outputs with retained forward images at the same target output
are equal under the supplied output bijection. No source-product matrix or
represented target graph is asserted. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputSourceSameImage

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductMatchFactorEquality
open PASoundness.PAtoCompactProductOutputImagePoint

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def rivalImage : Formula := replace 32 50 imageBody
def sameImageGuard : Formula := namedBoth firstBijection (namedBoth (.member 0 32)
  (namedBoth (.member 0 50) (namedBoth imageBody rivalImage)))
def originalFrame : Formula := .imp factorGuard (.imp (.equal 33 53) (.equal 30 50))

theorem relocated_frame_shape : replace 30 32 (replace 53 33 originalFrame) =
    .imp sameImageGuard (.imp (.equal 33 33) (.equal 32 50)) := by decide

def source_same_image : KDerivation (imp sameImageGuard.encode (equal 32 50)) := by
  have h0 : KDerivation originalFrame.encode := by
    simpa [originalFrame, CompactNamed.Formula.encode] using reflects_equality
  have h1 := replace_derivation 53 33 originalFrame (by decide) (by decide) h0
  have h2 := replace_derivation 30 32 (replace 53 33 originalFrame) (by decide) (by decide) h1
  have hf : KDerivation (imp sameImageGuard.encode (imp (equal 33 33) (equal 32 50))) := by
    simpa [relocated_frame_shape, CompactNamed.Formula.encode] using h2
  apply Context.closeEmpty
  apply Context.deduction
  have hg : Context [sameImageGuard.encode] sameImageGuard.encode := .head _ _
  exact .mp (.closed (equalityReflexive 33)) (.mp hg (.closed hf))

theorem source_same_image_certificate : theoremCode (certificate source_same_image) =
    imp sameImageGuard.encode (equal 32 50) := certificate_correct _

end PASoundness.PAtoCompactProductOutputSourceSameImage

#print axioms PASoundness.PAtoCompactProductOutputSourceSameImage.source_same_image
#print axioms PASoundness.PAtoCompactProductOutputSourceSameImage.source_same_image_certificate
