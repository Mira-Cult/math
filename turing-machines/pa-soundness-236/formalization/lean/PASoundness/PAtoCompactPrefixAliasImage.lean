import PASoundness.PAtoCompactPrefixAlias
import PASoundness.PAtoCompactPartialInverseImageWitness

/-! Existentially scoped endpoint alias and image witness for the exact
candidate bijection. This is a finite K proof: the chosen image is not
uniform, and no inverse-graph or successor invariant is established. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPrefixAliasImage
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPrefixAlias
open PASoundness.PAtoCompactPartialInverseImageWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The exact image-witness body, existentially binding the image name. -/
def imageAtAlias : Formula := .ex 13 (imageBody 12 13)

/-- The endpoint alias is existential, explicitly equated to old prefix 8. -/
def aliasImage : Nat := existsCode 12 (aliasBody imageAtAlias).encode

/-- If the actual bijection holds and the old prefix belongs to the source
domain, there are an endpoint alias equal to that prefix and an image witness
with the literal graph and uniqueness conditions. -/
def alias_image_exists : KDerivation
    (imp bijectionFormula.encode (imp (member 0 8) aliasImage)) := by
  have hi := universalInstance 2 8 imageClauseBody (by decide) (by decide) (by decide)
  have hinst : replace 2 8 imageClauseBody =
      .imp (.member 0 8) (.ex 3 (imageBody 8 3)) := by decide
  rw [hinst] at hi
  have ha := (existentialAlpha 3 13 (imageBody 8 3) (by decide) (by decide) (by decide)).1
  have hinstA : replace 3 13 (imageBody 8 3) = imageBody 8 13 := by decide
  rw [hinstA] at ha
  have hsubst : replace 12 8 imageAtAlias = .ex 13 (imageBody 8 13) := by decide
  have halias := alias_intro imageAtAlias (by decide) (by decide)
  rw [hsubst] at halias
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 0 8,bijectionFormula.encode]
  have hx : Context Γ (member 0 8) := Context.head _ _
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hl : Context Γ (allCode 2 imageClauseBody.encode) := Context.conjunctionLeft hb
  have hp : Context Γ (imp (member 0 8) (existsCode 3 (imageBody 8 3).encode)) :=
    .mp hl (.closed hi)
  have hw : Context Γ (existsCode 13 (imageBody 8 13).encode) :=
    .mp (.mp hx hp) (.closed ha)
  exact .mp hw (.closed halias)

theorem alias_image_exists_certificate : theoremCode (certificate alias_image_exists) =
    imp bijectionFormula.encode (imp (member 0 8) aliasImage) :=
  certificate_correct alias_image_exists

end PASoundness.PAtoCompactPrefixAliasImage

#print axioms PASoundness.PAtoCompactPrefixAliasImage.alias_image_exists
#print axioms PASoundness.PAtoCompactPrefixAliasImage.alias_image_exists_certificate
