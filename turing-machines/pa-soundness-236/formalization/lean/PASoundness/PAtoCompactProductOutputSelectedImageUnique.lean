import PASoundness.PAtoCompactProductOutputSelectedPath
import PASoundness.PAtoCompactProductOutputOutsidePath

/-! The output-bijection image of the selected source endpoint is unique:
a queried path at the same source endpoint has the selected target output.
No graph collection or factor-coordinate comparison is inferred. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputSelectedImageUnique

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactProductOutputImagePoint PASoundness.PAtoCompactProductOutputOutsidePath
open PASoundness.PAtoCompactProductOutputSelectedPath

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def selectedImage : Formula := replace 32 74 imageBody
def imageUnique : Formula := .imp
  (namedBoth (.member 42 4) (graphFormula 40 74 4)) (.equal 4 33)
def queriedImage : Formula := replace 33 60 imageBody

theorem selected_pair_shape : selectedPair = namedBoth (replace 32 74 sourceBody) selectedImage := by decide
theorem selected_image_shape : selectedImage = namedBoth (.member 42 33)
  (namedBoth (graphFormula 40 74 33) (.all 4 imageUnique)) := by decide
theorem query_image_shape : imageAt = queriedImage := by decide
theorem queried_image_shape : queriedImage = namedBoth (.member 42 60)
  (namedBoth (graphFormula 40 32 60) (.all 4 (.imp
    (namedBoth (.member 42 4) (graphFormula 40 32 4)) (.equal 4 60)))) := by decide

def same_source_image : KDerivation (imp selectedPair.encode (imp (equal 32 74)
    (imp payloadAt.encode (equal 60 33)))) := by
  have huni := universalInstance 4 60 imageUnique (by decide) (by decide) (by decide)
  have huniShape : replace 4 60 imageUnique = .imp
      (namedBoth (.member 42 60) (graphFormula 40 74 60)) (.equal 60 33) := by decide
  rw [huniShape] at huni
  have hmove := (equalityReplace 32 74 (graphFormula 40 32 60) (by decide) (by decide)).1
  have hmoveShape : replace 32 74 (graphFormula 40 32 60) = graphFormula 40 74 60 := by decide
  rw [hmoveShape] at hmove
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [payloadAt.encode,equal 32 74,selectedPair.encode]
  have hpay : Context Γ payloadAt.encode := .head _ _
  have he : Context Γ (equal 32 74) := .hypothesis (by simp [Γ])
  have hs : Context Γ selectedPair.encode := .hypothesis (by simp [Γ])
  have hpay' : Context Γ (both sourceAt.encode imageAt.encode) := by
    simpa [payload_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hpay
  have hquery : Context Γ (both (member 42 60) (both (graphFormula 40 32 60).encode
      (Formula.all 4 (.imp (namedBoth (.member 42 4) (graphFormula 40 32 4)) (.equal 4 60))).encode)) := by
    simpa [query_image_shape, queried_image_shape, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using Context.conjunctionRight hpay'
  have hs' : Context Γ (both (replace 32 74 sourceBody).encode selectedImage.encode) := by
    simpa [selected_pair_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hs
  have himage : Context Γ (both (member 42 33) (both (graphFormula 40 74 33).encode
      (allCode 4 imageUnique.encode))) := by
    simpa [selected_image_shape, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode,
      both, neg] using Context.conjunctionRight hs'
  have hedge := Context.mp (Context.conjunctionLeft (Context.conjunctionRight hquery))
    (Context.mp he (.closed hmove))
  have hguard : Context Γ (namedBoth (.member 42 60) (graphFormula 40 74 60)).encode := by
    simpa [namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro (Context.conjunctionLeft hquery) hedge
  have hu := Context.conjunctionRight (Context.conjunctionRight himage)
  have himp := Context.mp hu (.closed huni)
  simpa [CompactNamed.Formula.encode] using Context.mp hguard himp

theorem same_source_image_certificate : theoremCode (certificate same_source_image) =
    imp selectedPair.encode (imp (equal 32 74) (imp payloadAt.encode (equal 60 33))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputSelectedImageUnique

#print axioms PASoundness.PAtoCompactProductOutputSelectedImageUnique.same_source_image
#print axioms PASoundness.PAtoCompactProductOutputSelectedImageUnique.same_source_image_certificate
