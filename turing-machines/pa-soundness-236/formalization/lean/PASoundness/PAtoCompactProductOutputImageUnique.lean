import PASoundness.PAtoCompactProductOutputImagePoint

/-! Two retained source-product/output-image selections at one factor pair
have the same target output. This is pointwise and does not collect a graph. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputImageUnique

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductOutputImagePoint

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceUnique : Formula := .imp (namedBoth (.member 0 9) (tripleFormula 30 31 9)) (.equal 9 32)
def imageUnique : Formula := .imp (namedBoth (.member 42 4) (graphFormula 40 32 4)) (.equal 4 33)
def rivalSource : Formula := replace 32 50 sourceBody
def rivalImage : Formula := replace 33 51 (replace 32 50 imageBody)
def rivalPair : Formula := namedBoth rivalSource rivalImage

theorem source_shape : sourceBody = namedBoth (.member 0 32)
    (namedBoth (tripleFormula 30 31 32) (.all 9 sourceUnique)) := by decide
theorem rival_source_shape : rivalSource = namedBoth (.member 0 50)
    (namedBoth (tripleFormula 30 31 50) (.all 9 (replace 32 50 sourceUnique))) := by decide
theorem image_shape : imageBody = namedBoth (.member 42 33)
    (namedBoth (graphFormula 40 32 33) (.all 4 imageUnique)) := by decide
theorem rival_image_shape : rivalImage = namedBoth (.member 42 51)
    (namedBoth (graphFormula 40 50 51) (.all 4 (replace 33 51 (replace 32 50 imageUnique)))) := by decide

/-- Output uniqueness of the source product and isomorphism image compose,
keeping both selected bodies as literal antecedents. -/
def paired_image_unique : KDerivation
    (imp pairedBody.encode (imp rivalPair.encode (equal 51 33))) := by
  have hs := universalInstance 9 50 sourceUnique (by decide) (by decide) (by decide)
  have hss : replace 9 50 sourceUnique = .imp
      (namedBoth (.member 0 50) (tripleFormula 30 31 50)) (.equal 50 32) := by decide
  rw [hss] at hs
  have hi := universalInstance 4 51 imageUnique (by decide) (by decide) (by decide)
  have his : replace 4 51 imageUnique = .imp
      (namedBoth (.member 42 51) (graphFormula 40 32 51)) (.equal 51 33) := by decide
  rw [his] at hi
  have he := (equalityReplace 50 32 (graphFormula 40 50 51) (by decide) (by decide)).1
  have hes : replace 50 32 (graphFormula 40 50 51) = graphFormula 40 32 51 := by decide
  rw [hes] at he
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [rivalPair.encode,pairedBody.encode]
  have hr : Context Γ rivalPair.encode := .head _ _
  have hp : Context Γ pairedBody.encode := .hypothesis (by simp [Γ])
  have hp' : Context Γ (both sourceBody.encode imageBody.encode) := by
    simpa [pairedBody, namedBoth, Formula.not, Formula.encode, both, neg] using hp
  have hr' : Context Γ (both rivalSource.encode rivalImage.encode) := by
    simpa [rivalPair, namedBoth, Formula.not, Formula.encode, both, neg] using hr
  have hsource : Context Γ (both (member 0 32)
      (both (tripleFormula 30 31 32).encode (allCode 9 sourceUnique.encode))) := by
    simpa [source_shape, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionLeft hp'
  have hrival : Context Γ (both (member 0 50) (both (tripleFormula 30 31 50).encode
      (Formula.all 9 (replace 32 50 sourceUnique)).encode)) := by
    simpa [rival_source_shape, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionLeft hr'
  have himage : Context Γ (both (member 42 33)
      (both (graphFormula 40 32 33).encode (allCode 4 imageUnique.encode))) := by
    simpa [image_shape, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionRight hp'
  have hrimage : Context Γ (both (member 42 51) (both (graphFormula 40 50 51).encode
      (Formula.all 4 (replace 33 51 (replace 32 50 imageUnique))).encode)) := by
    simpa [rival_image_shape, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionRight hr'
  have hcomp := Context.conjunctionIntro (Context.conjunctionLeft hrival)
    (Context.conjunctionLeft (Context.conjunctionRight hrival))
  have heq : Context Γ (equal 50 32) := by
    have h := Context.mp hcomp (Context.mp (Context.conjunctionRight (Context.conjunctionRight hsource)) (.closed hs))
    simpa [namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hedge := Context.mp (Context.conjunctionLeft (Context.conjunctionRight hrimage)) (Context.mp heq (.closed he))
  have htarget := Context.conjunctionIntro (Context.conjunctionLeft hrimage) hedge
  have h := Context.mp htarget (Context.mp (Context.conjunctionRight (Context.conjunctionRight himage)) (.closed hi))
  simpa [Γ, namedBoth, Formula.not, Formula.encode, both, neg] using h

theorem paired_image_unique_certificate : theoremCode (certificate paired_image_unique) =
    imp pairedBody.encode (imp rivalPair.encode (equal 51 33)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputImageUnique

#print axioms PASoundness.PAtoCompactProductOutputImageUnique.paired_image_unique
#print axioms PASoundness.PAtoCompactProductOutputImageUnique.paired_image_unique_certificate
