import PASoundness.PAtoCompactProductMatchFactorEquality
import PASoundness.PAtoCompactScopedActiveReplace

/-! Reflect equality through the second factor bijection using its displayed
source memberships and forward images. Syntactic labels may denote equal values. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchMinorFactorReflection

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactProductMatchFactorEquality

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def reflectionFrame : Formula := .imp factorGuard (.imp (.equal 33 53) (.equal 30 50))
def minorGuard : Formula := replace 53 54 (replace 33 34 (replace 50 51 (replace 30 31
  (replace 0 1 (replace 42 43 (replace 40 41 factorGuard))))))
def minorFrame : Formula := .imp minorGuard (.imp (.equal 34 54) (.equal 31 51))

theorem minor_frame_shape : replace 53 54 (replace 33 34 (replace 50 51 (replace 30 31
    (replace 0 1 (replace 42 43 (replace 40 41 reflectionFrame)))))) = minorFrame := by decide

def minor_reflects_equality : KDerivation (imp minorGuard.encode
    (imp (equal 34 54) (equal 31 51))) := by
  have h0 : KDerivation reflectionFrame.encode := by simpa [reflectionFrame, Formula.encode] using reflects_equality
  have h1 := replace_derivation 40 41 reflectionFrame (by decide) (by decide) h0
  have h2 := replace_derivation 42 43 (replace 40 41 reflectionFrame) (by decide) (by decide) h1
  have h3 := replace_derivation 0 1 (replace 42 43 (replace 40 41 reflectionFrame)) (by decide) (by decide) h2
  have h4 := replace_derivation 30 31 (replace 0 1 (replace 42 43 (replace 40 41 reflectionFrame))) (by decide) (by decide) h3
  have h5 := replace_derivation 50 51 (replace 30 31 (replace 0 1 (replace 42 43 (replace 40 41 reflectionFrame)))) (by decide) (by decide) h4
  have h6 := replace_derivation 33 34 (replace 50 51 (replace 30 31 (replace 0 1 (replace 42 43 (replace 40 41 reflectionFrame))))) (by decide) (by decide) h5
  have h7 := replace_derivation 53 54 (replace 33 34 (replace 50 51 (replace 30 31 (replace 0 1 (replace 42 43 (replace 40 41 reflectionFrame)))))) (by decide) (by decide) h6
  rw [minor_frame_shape] at h7
  simpa [minorFrame, Formula.encode] using h7

theorem minor_reflects_equality_certificate : theoremCode (certificate minor_reflects_equality) =
    imp minorGuard.encode (imp (equal 34 54) (equal 31 51)) := certificate_correct _

end PASoundness.PAtoCompactProductMatchMinorFactorReflection

#print axioms PASoundness.PAtoCompactProductMatchMinorFactorReflection.minor_reflects_equality
#print axioms PASoundness.PAtoCompactProductMatchMinorFactorReflection.minor_reflects_equality_certificate
