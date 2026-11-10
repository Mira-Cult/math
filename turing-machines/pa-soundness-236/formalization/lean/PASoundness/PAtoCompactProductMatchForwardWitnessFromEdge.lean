import PASoundness.PAtoCompactProductMatchFactorImages
import PASoundness.PAtoCompactSuccGraphOutputLift
import PASoundness.PAtoCompactScopedActiveReplace

/-! Recover the forward-bijection witness clause for an already supplied
factor edge. This aligns reverse-selected preimages with the forward witness
shape used by product matching. It does not prove reverse-totality itself. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchForwardWitnessFromEdge

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuccGraphOutputLift PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactProductMatchFactorImages

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def majorGuard : Formula := namedBoth firstBijection (namedBoth (.member 0 30)
  (namedBoth (.member 42 33) (graphFormula 40 30 33)))
def witness53 : Formula := replace 33 53 firstImage
def unique53 : Formula := .imp (namedBoth (.member 42 4) (graphFormula 40 30 4)) (.equal 4 53)

theorem witness53_shape : witness53 = namedBoth (.member 42 53)
    (namedBoth (graphFormula 40 30 53) (.all 4 unique53)) := by decide

/-- The actual bijection and a displayed edge supply the complete forward
image witness at the displayed target. -/
def major_witness : KDerivation (imp firstBijection.encode (imp (member 0 30)
    (imp (member 42 33) (imp (graphFormula 40 30 33).encode firstImage.encode)))) := by
  have hi := universalInstance 4 33 unique53 (by decide) (by decide) (by decide)
  have hs : replace 4 33 unique53 =
      .imp (namedBoth (.member 42 33) (graphFormula 40 30 33)) (.equal 33 53) := by decide
  rw [hs] at hi
  have he := (equalityReplace 53 33 witness53 (by decide) (by decide)).1
  have heshape : replace 53 33 witness53 = firstImage := by decide
  rw [heshape] at he
  have hpoint : KDerivation (imp majorGuard.encode (imp witness53.encode firstImage.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [witness53.encode,majorGuard.encode]
    have hw : Context Γ witness53.encode := .head _ _
    have hg : Context Γ majorGuard.encode := .hypothesis (by simp [Γ])
    have hw' : Context Γ (both (member 42 53)
        (both (graphFormula 40 30 53).encode (allCode 4 unique53.encode))) := by
      simpa [witness53_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hw
    have hg' : Context Γ (both firstBijection.encode (both (member 0 30)
        (both (member 42 33) (graphFormula 40 30 33).encode))) := by
      simpa [majorGuard, namedBoth, Formula.not, Formula.encode, both, neg] using hg
    have hc := Context.conjunctionRight (Context.conjunctionRight hg')
    have hu := Context.conjunctionRight (Context.conjunctionRight hw')
    have heq : Context Γ (equal 33 53) := by
      have h := Context.mp hc (Context.mp hu (.closed hi))
      simpa [namedBoth, Formula.not, Formula.encode, both, neg] using h
    exact .mp hw (.mp (Context.eqSymm heq) (.closed he))
  have hv := majorGuard.vacuity 53 (by decide)
  have hq := firstImage.vacuity 53 (by decide)
  have helim := guarded_exists_left 53 majorGuard.encode witness53.encode firstImage.encode hv hq hpoint
  have ha := (existentialAlpha 33 53 firstImage (by decide) (by decide) (by decide)).1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 40 30 33).encode,member 42 33,member 0 30,firstBijection.encode]
  have he : Context Γ (graphFormula 40 30 33).encode := .head _ _
  have hy : Context Γ (member 42 33) := .hypothesis (by simp [Γ])
  have hx : Context Γ (member 0 30) := .hypothesis (by simp [Γ])
  have hb : Context Γ firstBijection.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ majorGuard.encode := by
    have h := Context.conjunctionIntro hb (Context.conjunctionIntro hx (Context.conjunctionIntro hy he))
    simpa [majorGuard, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hw : Context Γ (existsCode 33 firstImage.encode) := .mp hx (.mp hb (.closed first_image))
  have hw' : Context Γ (existsCode 53 witness53.encode) := by
    simpa [witness53] using Context.mp hw (.closed ha)
  exact .mp hw' (.mp hg (.closed helim))

def majorFrame : Formula := .imp firstBijection (.imp (.member 0 30)
  (.imp (.member 42 33) (.imp (graphFormula 40 30 33) firstImage)))
def minorFrame : Formula := .imp secondBijection (.imp (.member 1 31)
  (.imp (.member 43 34) (.imp (graphFormula 41 31 34) secondImage)))

theorem minor_relocation : replace 33 34 (replace 30 31 (replace 40 41
    (replace 42 43 (replace 0 1 majorFrame)))) = minorFrame := by decide

/-- The same exact forward-witness reconstruction for the minor factor. -/
def minor_witness : KDerivation (imp secondBijection.encode (imp (member 1 31)
    (imp (member 43 34) (imp (graphFormula 41 31 34).encode secondImage.encode)))) := by
  have h0 : KDerivation majorFrame.encode := by simpa [majorFrame, Formula.encode] using major_witness
  have h1 := replace_derivation 0 1 majorFrame (by decide) (by decide) h0
  have h2 := replace_derivation 42 43 (replace 0 1 majorFrame) (by decide) (by decide) h1
  have h3 := replace_derivation 40 41 (replace 42 43 (replace 0 1 majorFrame))
    (by decide) (by decide) h2
  have h4 := replace_derivation 30 31 (replace 40 41 (replace 42 43 (replace 0 1 majorFrame)))
    (by decide) (by decide) h3
  have h5 := replace_derivation 33 34
    (replace 30 31 (replace 40 41 (replace 42 43 (replace 0 1 majorFrame))))
    (by decide) (by decide) h4
  rw [minor_relocation] at h5
  simpa [minorFrame, Formula.encode] using h5

theorem major_witness_certificate : theoremCode (certificate major_witness) =
    imp firstBijection.encode (imp (member 0 30) (imp (member 42 33)
      (imp (graphFormula 40 30 33).encode firstImage.encode))) := certificate_correct _
theorem minor_witness_certificate : theoremCode (certificate minor_witness) =
    imp secondBijection.encode (imp (member 1 31) (imp (member 43 34)
      (imp (graphFormula 41 31 34).encode secondImage.encode))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchForwardWitnessFromEdge

#print axioms PASoundness.PAtoCompactProductMatchForwardWitnessFromEdge.major_witness
#print axioms PASoundness.PAtoCompactProductMatchForwardWitnessFromEdge.minor_witness
#print axioms PASoundness.PAtoCompactProductMatchForwardWitnessFromEdge.major_witness_certificate
#print axioms PASoundness.PAtoCompactProductMatchForwardWitnessFromEdge.minor_witness_certificate
