import PASoundness.PAtoCompactProductMatchBothImages
import PASoundness.PAtoCompactProductMatchTargetOutput

/-! Construct one target-product output matching a selected source-product
coordinate pair through two supplied factor bijections. All factor and
target-product witness clauses remain attached. This is one local match,
not a collected represented graph or a full product isomorphism. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchTargetWitness

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactProductMatchPointWitness
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductMatchBothImages
open PASoundness.PAtoCompactProductMatchTargetOutput

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def matchBody : Formula := namedBoth bothImages targetOutputBody

/-- Given the selected factor images and target product matrix, retain both
image witnesses while choosing the target output. -/
def target_from_images : KDerivation
    (imp targetMatrix.encode (imp bothImages.encode (existsCode 35 matchBody.encode))) := by
  let I := bothImages.encode
  let O := targetOutputBody.encode
  let P := matchBody.encode
  have hlocal : KDerivation (imp I (imp O P)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [O,I]
    have ho : Context Γ O := .head _ _
    have hi : Context Γ I := .hypothesis (by simp [Γ])
    have hp := Context.conjunctionIntro hi ho
    simpa [P, I, O, matchBody, namedBoth, Formula.not, Formula.encode, both, neg] using hp
  have hv : KDerivation (imp I (allCode 35 I)) := bothImages.vacuity 35 (by decide)
  have hpack := conditionalExistsCongr 35 hv hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [I,targetMatrix.encode]
  have hi : Context Γ I := .head _ _
  have hm : Context Γ targetMatrix.encode := .hypothesis (by simp [Γ])
  have hi' : Context Γ (both firstImage.encode secondImage.encode) := by
    simpa [I, bothImages, namedBoth, Formula.not, Formula.encode, both, neg] using hi
  have hf : Context Γ firstImage.encode := Context.conjunctionLeft hi'
  have hs : Context Γ secondImage.encode := Context.conjunctionRight hi'
  have hf' : Context Γ (both (member 42 33)
      (both (graphFormula 40 30 33).encode
        (Formula.all 4 (Formula.imp (namedBoth (.member 42 4)
          (graphFormula 40 30 4)) (.equal 4 33))).encode)) := by
    simpa [firstImage, namedBoth, Formula.not, Formula.encode, both, neg] using hf
  have hs' : Context Γ (both (member 43 34)
      (both (graphFormula 41 31 34).encode
        (Formula.all 4 (Formula.imp (namedBoth (.member 43 4)
          (graphFormula 41 31 4)) (.equal 4 34))).encode)) := by
    simpa [secondImage, namedBoth, Formula.not, Formula.encode, both, neg] using hs
  have hx : Context Γ (member 42 33) := Context.conjunctionLeft hf'
  have hy : Context Γ (member 43 34) := Context.conjunctionLeft hs'
  have ho : Context Γ (existsCode 35 O) := .mp hy (.mp hx (.mp hm (.closed target_output)))
  exact .mp ho (.mp hi (.closed hpack))

/-- From selected source coordinates, two factor bijections and the target
product matrix, choose both factor images and one target-product output. -/
def matched_target_exists : KDerivation
    (imp selectedReverseBody.encode (imp firstBijection.encode (imp secondBijection.encode
      (imp targetMatrix.encode (existsCode 33 (existsCode 34 (existsCode 35 matchBody.encode))))))) := by
  have hv₃₄ := targetMatrix.vacuity 34 (by decide)
  have hv₃₃ := targetMatrix.vacuity 33 (by decide)
  have h34 := conditionalExistsCongr 34 hv₃₄ target_from_images
  have h33 := conditionalExistsCongr 33 hv₃₃ h34
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [targetMatrix.encode,secondBijection.encode,firstBijection.encode,selectedReverseBody.encode]
  have hm : Context Γ targetMatrix.encode := .head _ _
  have hb₂ : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hb₁ : Context Γ firstBijection.encode := .hypothesis (by simp [Γ])
  have hr : Context Γ selectedReverseBody.encode := .hypothesis (by simp [Γ])
  have hi := Context.mp hb₂ (Context.mp hb₁ (Context.mp hr (.closed both_images)))
  exact .mp hi (.mp hm (.closed h33))

theorem matched_target_exists_certificate : theoremCode (certificate matched_target_exists) =
    imp selectedReverseBody.encode (imp firstBijection.encode (imp secondBijection.encode
      (imp targetMatrix.encode (existsCode 33 (existsCode 34 (existsCode 35 matchBody.encode)))))) :=
  certificate_correct _

end PASoundness.PAtoCompactProductMatchTargetWitness

#print axioms PASoundness.PAtoCompactProductMatchTargetWitness.target_from_images
#print axioms PASoundness.PAtoCompactProductMatchTargetWitness.matched_target_exists
#print axioms PASoundness.PAtoCompactProductMatchTargetWitness.matched_target_exists_certificate
