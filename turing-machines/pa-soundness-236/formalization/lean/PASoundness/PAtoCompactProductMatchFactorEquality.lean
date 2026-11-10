import PASoundness.PAtoCompactProductMatchReverseFactors
import PASoundness.PAtoCompactSuccGraphOutputLift

/-! Pointwise equality reflection/preservation for two selected images of a
single supplied factor bijection. The factor guard, both displayed image
clauses and source memberships are explicit; this is not a match-graph
order or product-congruence theorem. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchFactorEquality

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuccGraphOutputLift PASoundness.PAtoCompactProductMatchFactorImages
open PASoundness.PAtoCompactProductMatchReverseFactors

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def otherImage : Formula := replace 33 53 (replace 30 50 firstImage)
def factorGuard : Formula := namedBoth firstBijection (namedBoth (.member 0 30)
  (namedBoth (.member 0 50) (namedBoth firstImage otherImage)))
def reverseGuard : Formula := namedBoth factorGuard (.equal 33 53)
def preimage60 : Formula := replace 30 60 majorPreimage
def preimageUnique : Formula := .imp (namedBoth (.member 0 4) (graphFormula 40 4 33)) (.equal 4 60)

theorem other_image_shape : otherImage = namedBoth (.member 42 53)
    (namedBoth (graphFormula 40 50 53) (.all 4 (.imp
      (namedBoth (.member 42 4) (graphFormula 40 50 4)) (.equal 4 53)))) := by decide

theorem preimage60_shape : preimage60 = namedBoth (.member 0 60)
    (namedBoth (graphFormula 40 60 33) (.all 4 preimageUnique)) := by decide

/-- Identical source coordinates have identical displayed target images. -/
def preserves_equality : KDerivation (imp factorGuard.encode
    (imp (equal 30 50) (equal 33 53))) := by
  let F : Formula := .imp (namedBoth (.member 42 4) (graphFormula 40 50 4)) (.equal 4 53)
  have hi := universalInstance 4 33 F (by decide) (by decide) (by decide)
  have hs : replace 4 33 F =
      .imp (namedBoth (.member 42 33) (graphFormula 40 50 33)) (.equal 33 53) := by decide
  rw [hs] at hi
  have he := (equalityReplace 30 50 (graphFormula 40 30 33) (by decide) (by decide)).1
  have hes : replace 30 50 (graphFormula 40 30 33) = graphFormula 40 50 33 := by decide
  rw [hes] at he
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal 30 50,factorGuard.encode]
  have hx : Context Γ (equal 30 50) := .head _ _
  have hg : Context Γ factorGuard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both firstBijection.encode (both (member 0 30)
      (both (member 0 50) (both firstImage.encode otherImage.encode)))) := by
    simpa [factorGuard, namedBoth, Formula.not, Formula.encode, both, neg] using hg
  have hf := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg')))
  have ho := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg')))
  have hf' : Context Γ (both (member 42 33) (both (graphFormula 40 30 33).encode
      (Formula.all 4 (.imp (namedBoth (.member 42 4) (graphFormula 40 30 4)) (.equal 4 33))).encode)) := by
    simpa [firstImage, namedBoth, Formula.not, Formula.encode, both, neg] using hf
  have ho' : Context Γ (both (member 42 53) (both (graphFormula 40 50 53).encode (allCode 4 F.encode))) := by
    simpa [other_image_shape, F, namedBoth, Formula.not, Formula.encode, both, neg] using ho
  have hedge := Context.conjunctionLeft (Context.conjunctionRight hf')
  have hedge' := Context.mp hedge (Context.mp hx (.closed he))
  have hc := Context.conjunctionIntro (Context.conjunctionLeft hf') hedge'
  have hu := Context.conjunctionRight (Context.conjunctionRight ho')
  have h := Context.mp hc (Context.mp hu (.closed hi))
  simpa [Formula.encode, namedBoth, Formula.not, both, neg] using h

/-- Identical target images have identical source coordinates; the supplied
reverse-bijection witness is existentially selected and eliminated. -/
def reflects_equality : KDerivation (imp factorGuard.encode
    (imp (equal 33 53) (equal 30 50))) := by
  have h₁ := universalInstance 4 30 preimageUnique (by decide) (by decide) (by decide)
  have hs₁ : replace 4 30 preimageUnique =
      .imp (namedBoth (.member 0 30) (graphFormula 40 30 33)) (.equal 30 60) := by decide
  rw [hs₁] at h₁
  have h₂ := universalInstance 4 50 preimageUnique (by decide) (by decide) (by decide)
  have hs₂ : replace 4 50 preimageUnique =
      .imp (namedBoth (.member 0 50) (graphFormula 40 50 33)) (.equal 50 60) := by decide
  rw [hs₂] at h₂
  have ht := (equalityReplace 53 33 (graphFormula 40 50 53) (by decide) (by decide)).1
  have hts : replace 53 33 (graphFormula 40 50 53) = graphFormula 40 50 33 := by decide
  rw [hts] at ht
  have hpoint : KDerivation (imp reverseGuard.encode (imp preimage60.encode (equal 30 50))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [preimage60.encode,reverseGuard.encode]
    have hp : Context Γ preimage60.encode := .head _ _
    have hg : Context Γ reverseGuard.encode := .hypothesis (by simp [Γ])
    have hp' : Context Γ (both (member 0 60) (both (graphFormula 40 60 33).encode
        (allCode 4 preimageUnique.encode))) := by
      simpa [preimage60_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hp
    have hg' : Context Γ (both factorGuard.encode (equal 33 53)) := by
      simpa [reverseGuard, namedBoth, Formula.not, Formula.encode, both, neg] using hg
    have hF := Context.conjunctionLeft hg'
    have hy := Context.conjunctionRight hg'
    have hF' : Context Γ (both firstBijection.encode (both (member 0 30)
        (both (member 0 50) (both firstImage.encode otherImage.encode)))) := by
      simpa [factorGuard, namedBoth, Formula.not, Formula.encode, both, neg] using hF
    have hx₁ := Context.conjunctionLeft (Context.conjunctionRight hF')
    have hx₂ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hF'))
    have hf := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hF')))
    have ho := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hF')))
    have hf' : Context Γ (both (member 42 33) (both (graphFormula 40 30 33).encode
        (Formula.all 4 (.imp (namedBoth (.member 42 4) (graphFormula 40 30 4)) (.equal 4 33))).encode)) := by
      simpa [firstImage, namedBoth, Formula.not, Formula.encode, both, neg] using hf
    have ho' : Context Γ (both (member 42 53) (both (graphFormula 40 50 53).encode
        (Formula.all 4 (.imp (namedBoth (.member 42 4) (graphFormula 40 50 4)) (.equal 4 53))).encode)) := by
      simpa [other_image_shape, namedBoth, Formula.not, Formula.encode, both, neg] using ho
    have hg₁ := Context.conjunctionLeft (Context.conjunctionRight hf')
    have hg₂ := Context.conjunctionLeft (Context.conjunctionRight ho')
    have hg₂' := Context.mp hg₂ (Context.mp (Context.eqSymm hy) (.closed ht))
    have hu := Context.conjunctionRight (Context.conjunctionRight hp')
    have he₁ : Context Γ (equal 30 60) := by
      have h := Context.mp (Context.conjunctionIntro hx₁ hg₁) (Context.mp hu (.closed h₁))
      simpa [namedBoth, Formula.not, Formula.encode, both, neg] using h
    have he₂ : Context Γ (equal 50 60) := by
      have h := Context.mp (Context.conjunctionIntro hx₂ hg₂') (Context.mp hu (.closed h₂))
      simpa [namedBoth, Formula.not, Formula.encode, both, neg] using h
    exact Context.eqTrans he₁ (Context.eqSymm he₂)
  let E : Formula := .equal 30 50
  have helim := guarded_exists_left 60 reverseGuard.encode preimage60.encode E.encode
    (reverseGuard.vacuity 60 (by decide)) (E.vacuity 60 (by decide)) hpoint
  have ha := (existentialAlpha 30 60 majorPreimage (by decide) (by decide) (by decide)).1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal 33 53,factorGuard.encode]
  have hy : Context Γ (equal 33 53) := .head _ _
  have hg : Context Γ factorGuard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both firstBijection.encode (both (member 0 30)
      (both (member 0 50) (both firstImage.encode otherImage.encode)))) := by
    simpa [factorGuard, namedBoth, Formula.not, Formula.encode, both, neg] using hg
  have hb := Context.conjunctionLeft hg'
  have hf := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg')))
  have hf' : Context Γ (both (member 42 33) (both (graphFormula 40 30 33).encode
      (Formula.all 4 (.imp (namedBoth (.member 42 4) (graphFormula 40 30 4)) (.equal 4 33))).encode)) := by
    simpa [firstImage, namedBoth, Formula.not, Formula.encode, both, neg] using hf
  have hw : Context Γ (existsCode 30 majorPreimage.encode) :=
    .mp (Context.conjunctionLeft hf') (.mp hb (.closed major_preimage))
  have hw' : Context Γ (existsCode 60 preimage60.encode) := by
    simpa [preimage60] using Context.mp hw (.closed ha)
  have hguard : Context Γ reverseGuard.encode := by
    have h := Context.conjunctionIntro hg hy
    simpa [reverseGuard, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have h := Context.mp hw' (Context.mp hguard (.closed helim))
  simpa [Γ, E, Formula.encode] using h

/-- The two equality directions, with no distinctness assumption on values. -/
def equality_comparison : KDerivation (imp factorGuard.encode
    (both (imp (equal 30 50) (equal 33 53)) (imp (equal 33 53) (equal 30 50)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  have hg : Context [factorGuard.encode] factorGuard.encode := .head _ _
  exact Context.conjunctionIntro (.mp hg (.closed preserves_equality))
    (.mp hg (.closed reflects_equality))

theorem equality_comparison_certificate : theoremCode (certificate equality_comparison) =
    imp factorGuard.encode (both (imp (equal 30 50) (equal 33 53))
      (imp (equal 33 53) (equal 30 50))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchFactorEquality

#print axioms PASoundness.PAtoCompactProductMatchFactorEquality.preserves_equality
#print axioms PASoundness.PAtoCompactProductMatchFactorEquality.reflects_equality
#print axioms PASoundness.PAtoCompactProductMatchFactorEquality.equality_comparison
#print axioms PASoundness.PAtoCompactProductMatchFactorEquality.equality_comparison_certificate
