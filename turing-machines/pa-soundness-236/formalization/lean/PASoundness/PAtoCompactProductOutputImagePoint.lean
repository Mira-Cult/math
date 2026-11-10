import PASoundness.PAtoCompactProductMatchPointWitness
import PASoundness.PAtoCompactProductMatchPointUnique
import PASoundness.PAtoCompactProductMatchFactorImages
import PASoundness.PAtoCompactScopedActiveReplace

/-! Retain a source product triple and an image under an output isomorphism
at the same source-output witness. This is pointwise input to a future
represented triple-graph collection; no graph collection is asserted. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputImagePoint

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductMatchPointWitness PASoundness.PAtoCompactProductMatchFactorImages
open PASoundness.PAtoCompactScopedActiveReplace

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Source factor labels 80,81 and source product-output domain 0. -/
def sourceMatrix : Formula := replace 2 0 (replace 1 81 (replace 0 80 productMatrix))
def sourceBody : Formula := replace 2 0 (replace 1 81 (replace 0 80 selectedForwardBody))
def sourceFrame : Formula := .imp productMatrix (.imp (.member 0 30)
  (.imp (.member 1 31) (.ex 32 selectedForwardBody)))
def relocatedFrame : Formula := .imp sourceMatrix (.imp (.member 80 30)
  (.imp (.member 81 31) (.ex 32 sourceBody)))
def imageBody : Formula := replace 30 32 firstImage
def pairedBody : Formula := namedBoth sourceBody imageBody

theorem source_frame_shape : replace 2 0 (replace 1 81 (replace 0 80 sourceFrame)) = relocatedFrame := by decide
theorem source_body_shape : sourceBody = namedBoth (.member 0 32)
    (namedBoth (replace 2 0 (replace 1 81 (replace 0 80 (tripleFormula 30 31 32))))
      (replace 2 0 (replace 1 81 (replace 0 80
        (.all 9 PAtoCompactProductMatchPointUnique.forwardUnique))))) := by decide
theorem image_frame_shape : replace 30 32 firstFrame = .imp firstBijection
    (.imp (.member 0 32) (.ex 33 imageBody)) := by decide

def source_output : KDerivation (imp sourceMatrix.encode (imp (member 80 30)
    (imp (member 81 31) (existsCode 32 sourceBody.encode)))) := by
  have h0 : KDerivation sourceFrame.encode := by simpa [sourceFrame, Formula.encode] using forward_output
  have h1 := replace_derivation 0 80 sourceFrame (by decide) (by decide) h0
  have h2 := replace_derivation 1 81 (replace 0 80 sourceFrame) (by decide) (by decide) h1
  have h3 := replace_derivation 2 0 (replace 1 81 (replace 0 80 sourceFrame)) (by decide) (by decide) h2
  rw [source_frame_shape] at h3
  simpa [relocatedFrame, Formula.encode] using h3

def output_image : KDerivation (imp firstBijection.encode (imp (member 0 32)
    (existsCode 33 imageBody.encode))) := by
  have h0 : KDerivation firstFrame.encode := by simpa [first_frame_shape, Formula.encode] using first_image
  have h1 := replace_derivation 30 32 firstFrame (by decide) (by decide) h0
  rw [image_frame_shape] at h1
  simpa [Formula.encode] using h1

def output_image_retained : KDerivation (imp firstBijection.encode (imp sourceBody.encode
    (existsCode 33 pairedBody.encode))) := by
  have hpoint : KDerivation (imp sourceBody.encode (imp imageBody.encode pairedBody.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [imageBody.encode,sourceBody.encode]
    have hi : Context Γ imageBody.encode := .head _ _
    have hs : Context Γ sourceBody.encode := .hypothesis (by simp [Γ])
    simpa [Γ, pairedBody, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionIntro hs hi
  have hlift := conditionalExistsCongr 33 (sourceBody.vacuity 33 (by decide)) hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [sourceBody.encode,firstBijection.encode]
  have hs : Context Γ sourceBody.encode := .head _ _
  have hb : Context Γ firstBijection.encode := .hypothesis (by simp [Γ])
  have hs' : Context Γ (both (member 0 32)
      (both (replace 2 0 (replace 1 81 (replace 0 80 (tripleFormula 30 31 32)))).encode
        (replace 2 0 (replace 1 81 (replace 0 80
          (.all 9 PAtoCompactProductMatchPointUnique.forwardUnique)))).encode)) := by
    simpa [source_body_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hs
  have hw := Context.mp (Context.conjunctionLeft hs') (Context.mp hb (.closed output_image))
  simpa [Γ] using Context.mp hw (Context.mp hs (.closed hlift))

def paired_output_exists : KDerivation (imp sourceMatrix.encode (imp firstBijection.encode
    (imp (member 80 30) (imp (member 81 31)
      (existsCode 32 (existsCode 33 pairedBody.encode)))))) := by
  have hlift := conditionalExistsCongr 32 (firstBijection.vacuity 32 (by decide)) output_image_retained
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 81 31,member 80 30,firstBijection.encode,sourceMatrix.encode]
  have hy : Context Γ (member 81 31) := .head _ _
  have hx : Context Γ (member 80 30) := .hypothesis (by simp [Γ])
  have hi : Context Γ firstBijection.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ sourceMatrix.encode := .hypothesis (by simp [Γ])
  have hs := Context.mp hy (Context.mp hx (Context.mp hm (.closed source_output)))
  simpa [Γ] using Context.mp hs (Context.mp hi (.closed hlift))

theorem paired_output_exists_certificate : theoremCode (certificate paired_output_exists) =
    imp sourceMatrix.encode (imp firstBijection.encode (imp (member 80 30)
      (imp (member 81 31) (existsCode 32 (existsCode 33 pairedBody.encode))))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputImagePoint

#print axioms PASoundness.PAtoCompactProductOutputImagePoint.source_output
#print axioms PASoundness.PAtoCompactProductOutputImagePoint.output_image
#print axioms PASoundness.PAtoCompactProductOutputImagePoint.output_image_retained
#print axioms PASoundness.PAtoCompactProductOutputImagePoint.paired_output_exists
#print axioms PASoundness.PAtoCompactProductOutputImagePoint.paired_output_exists_certificate
