import PASoundness.PAtoCompactCompositionSelectedImages
import PASoundness.PAtoCompactScopedActiveReplace

/-! Factor-isomorphism image witnesses for matching product edges. Each
supplied factor bijection chooses an image and retains its exact uniqueness
clause. The two images have not yet been collected into a match graph. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchFactorImages

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactCompositionSelectedImages
open PASoundness.PAtoCompactScopedActiveReplace

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def baseFrame (n : Nat) : Formula := .imp bijectionFormula
  (.imp (.member 0 10) (.ex n (replace 11 n firstImageBody)))

/-- Retain the selected bijection-image uniqueness clause while moving its
existential output binder to an explicit fresh name. -/
def base_image (n : Nat) (hne : 11 ≠ n) (hn : n ∉ firstImageBody.names) :
    KDerivation (baseFrame n).encode := by
  have ha := (existentialAlpha 11 n firstImageBody hne (by decide) hn).1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 0 10, bijectionFormula.encode]
  have hx : Context Γ (member 0 10) := .head _ _
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hw := Context.mp hx (Context.mp hb (.closed first_image_exists))
  simpa [baseFrame, Formula.encode] using Context.mp hw (.closed ha)

def firstBijection : Formula := replace 1 42 (replace 6 40 bijectionFormula)
def firstImage : Formula := namedBoth (.member 42 33)
  (namedBoth (graphFormula 40 30 33)
    (.all 4 (.imp (namedBoth (.member 42 4) (graphFormula 40 30 4)) (.equal 4 33))))

def firstFrame : Formula := replace 10 30 (replace 1 42 (replace 6 40 (baseFrame 33)))

theorem first_frame_shape : firstFrame =
    .imp firstBijection (.imp (.member 0 30) (.ex 33 firstImage)) := by decide

/-- The major-factor bijection sends source coordinate 30 to a member 33 of
target factor 42, retaining its graph edge and unique-image clause. -/
def first_image : KDerivation
    (imp firstBijection.encode (imp (member 0 30) (existsCode 33 firstImage.encode))) := by
  have h0 := base_image 33 (by decide) (by decide)
  have h1 := replace_derivation 6 40 (baseFrame 33) (by decide) (by decide) h0
  have h2 := replace_derivation 1 42 (replace 6 40 (baseFrame 33)) (by decide) (by decide) h1
  have h3 := replace_derivation 10 30 (replace 1 42 (replace 6 40 (baseFrame 33)))
    (by decide) (by decide) h2
  change KDerivation firstFrame.encode at h3
  rw [first_frame_shape] at h3
  simpa [Formula.encode] using h3

def secondBijection : Formula := replace 0 1 (replace 1 43 (replace 6 41 bijectionFormula))
def secondImage : Formula := namedBoth (.member 43 34)
  (namedBoth (graphFormula 41 31 34)
    (.all 4 (.imp (namedBoth (.member 43 4) (graphFormula 41 31 4)) (.equal 4 34))))

def secondFrame : Formula :=
  replace 10 31 (replace 0 1 (replace 1 43 (replace 6 41 (baseFrame 34))))

theorem second_frame_shape : secondFrame =
    .imp secondBijection (.imp (.member 1 31) (.ex 34 secondImage)) := by decide

/-- The minor-factor bijection sends source coordinate 31 to a member 34 of
target factor 43, retaining its graph edge and unique-image clause. -/
def second_image : KDerivation
    (imp secondBijection.encode (imp (member 1 31) (existsCode 34 secondImage.encode))) := by
  have h0 := base_image 34 (by decide) (by decide)
  have h1 := replace_derivation 6 41 (baseFrame 34) (by decide) (by decide) h0
  have h2 := replace_derivation 1 43 (replace 6 41 (baseFrame 34)) (by decide) (by decide) h1
  have h3 := replace_derivation 0 1 (replace 1 43 (replace 6 41 (baseFrame 34)))
    (by decide) (by decide) h2
  have h4 := replace_derivation 10 31
    (replace 0 1 (replace 1 43 (replace 6 41 (baseFrame 34)))) (by decide) (by decide) h3
  change KDerivation secondFrame.encode at h4
  rw [second_frame_shape] at h4
  simpa [Formula.encode] using h4

theorem first_image_certificate : theoremCode (certificate first_image) =
    imp firstBijection.encode (imp (member 0 30) (existsCode 33 firstImage.encode)) :=
  certificate_correct _

theorem second_image_certificate : theoremCode (certificate second_image) =
    imp secondBijection.encode (imp (member 1 31) (existsCode 34 secondImage.encode)) :=
  certificate_correct _

end PASoundness.PAtoCompactProductMatchFactorImages

#print axioms PASoundness.PAtoCompactProductMatchFactorImages.base_image
#print axioms PASoundness.PAtoCompactProductMatchFactorImages.first_image
#print axioms PASoundness.PAtoCompactProductMatchFactorImages.second_image
#print axioms PASoundness.PAtoCompactProductMatchFactorImages.first_image_certificate
#print axioms PASoundness.PAtoCompactProductMatchFactorImages.second_image_certificate
