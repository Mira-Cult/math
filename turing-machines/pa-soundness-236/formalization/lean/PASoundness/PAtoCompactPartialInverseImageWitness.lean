import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactDerivations

/-! Expose one image witness of the exact original bijection clause at a
specified source endpoint. The existential witness remains explicit, and no
uniform choice or inverse graph is constructed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseImageWitness
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

def imageBody (source image : Nat) : Formula :=
  conj (.member 1 image) (conj (graphFormula 6 source image)
    (.all 4 (.imp (conj (.member 1 4) (graphFormula 6 source 4)) (.equal 4 image))))

def imageWitness : Nat := (imageBody 12 13).encode

/-- The literal first bijection conjunct, factored to display its source
binder and image witness. -/
def imageClauseBody : Formula := .imp (.member 0 2) (.ex 3 (imageBody 2 3))

/-- Given the actual bijection and an endpoint 12 in source domain 0, K
constructs the existence of one target-domain image 13, its old edge, and
its complete uniqueness condition. -/
def endpoint_image_exists : KDerivation
    (imp bijectionFormula.encode (imp (member 0 12) (existsCode 13 imageWitness))) := by
  have hi := universalInstance 2 12 imageClauseBody (by decide) (by decide) (by decide)
  have hinst : replace 2 12 imageClauseBody =
      .imp (.member 0 12) (.ex 3 (imageBody 12 3)) := by decide
  rw [hinst] at hi
  have ha := (existentialAlpha 3 13 (imageBody 12 3) (by decide) (by decide) (by decide)).1
  have hinstA : replace 3 13 (imageBody 12 3) = imageBody 12 13 := by decide
  rw [hinstA] at ha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 0 12,bijectionFormula.encode]
  have hx : Context Γ (member 0 12) := Context.head _ _
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hl : Context Γ (allCode 2 imageClauseBody.encode) := Context.conjunctionLeft hb
  have hp : Context Γ (imp (member 0 12) (existsCode 3 (imageBody 12 3).encode)) :=
    .mp hl (.closed hi)
  exact .mp (.mp hx hp) (.closed ha)

theorem endpoint_image_exists_certificate : theoremCode (certificate endpoint_image_exists) =
    imp bijectionFormula.encode (imp (member 0 12) (existsCode 13 imageWitness)) :=
  certificate_correct endpoint_image_exists

end PASoundness.PAtoCompactPartialInverseImageWitness

#print axioms PASoundness.PAtoCompactPartialInverseImageWitness.endpoint_image_exists
#print axioms PASoundness.PAtoCompactPartialInverseImageWitness.endpoint_image_exists_certificate
