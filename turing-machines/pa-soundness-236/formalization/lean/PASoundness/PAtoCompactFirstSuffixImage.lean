import PASoundness.PAtoCompactSecondSuffixImage
import PASoundness.PAtoCompactFirstSuffixInverseSelected

/-! The first suffix bijection supplies an image of common-source point42.
The target witness is alpha-renamed from 3 to 2 while keeping its actual
suffix membership and graph6 edge together. -/
namespace PASoundness.PAtoCompactFirstSuffixImage

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactScopedActiveReplace

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def suffixBijection : Formula := PASoundness.PAtoCompactFirstSuffixInverseSelected.suffixBijection
private def secondBijection : Formula := PASoundness.PAtoCompactSecondSuffixForwardSelected.suffixBijection
private def frame : Formula := .imp secondBijection (.imp (.member 1 42)
  PASoundness.PAtoCompactSecondSuffixImage.image)
private def f31 : Formula := replace 38 31 frame
private def body3 : Formula := namedBoth (.member 31 3) (graphFormula 6 42 3)
def imageBody : Formula := namedBoth (.member 31 2) (graphFormula 6 42 2)
def image : Formula := .ex 2 imageBody
private theorem frame_alignment : replace 7 6 f31 = .imp suffixBijection
  (.imp (.member 1 42) (.ex 3 body3)) := by decide
private theorem body_alignment : replace 3 2 body3 = imageBody := by decide

/-- The same image witness has literal suffix31 membership and graph6 edge. -/
def first_suffix_image : KDerivation (imp suffixBijection.encode
    (imp (member 1 42) image.encode)) := by
  have hbase : KDerivation frame.encode := by
    simpa only [frame,secondBijection,Formula.encode] using PASoundness.PAtoCompactSecondSuffixImage.second_suffix_image
  have h31 := replace_derivation 38 31 frame (by decide) (by decide) hbase
  have h6 := replace_derivation 7 6 f31 (by decide) (by decide) (by simpa only [f31] using h31)
  rw [frame_alignment] at h6
  have ha := (existentialAlpha 3 2 body3 (by decide) (by decide) (by decide)).1
  rw [body_alignment] at ha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 1 42,suffixBijection.encode]
  have hm : Context Γ (member 1 42) := .head _ _
  have hb : Context Γ suffixBijection.encode := .hypothesis (by simp [Γ])
  have he : Context Γ (existsCode 3 body3.encode) := .mp hm (.mp hb (.closed h6))
  exact .mp he (.closed ha)

theorem first_suffix_image_certificate : theoremCode (certificate first_suffix_image) =
    imp suffixBijection.encode (imp (member 1 42) image.encode) := certificate_correct first_suffix_image

end PASoundness.PAtoCompactFirstSuffixImage

#print axioms PASoundness.PAtoCompactFirstSuffixImage.suffixBijection
#print axioms PASoundness.PAtoCompactFirstSuffixImage.imageBody
#print axioms PASoundness.PAtoCompactFirstSuffixImage.image
#print axioms PASoundness.PAtoCompactFirstSuffixImage.first_suffix_image
#print axioms PASoundness.PAtoCompactFirstSuffixImage.first_suffix_image_certificate
