import PASoundness.PAtoCompactBijectionBackwardAtThree
import PASoundness.PAtoCompactScopedActiveReplace
import PASoundness.PAtoCompactProductMatchFactorImages

/-! Reverse preimage witnesses for the two supplied product-factor
bijections. The witnesses retain the original directed edges and the
reverse-uniqueness clauses. They do not yet establish a reverse product match. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchReverseFactors

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactBijectionBackwardAtThree PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactProductMatchFactorImages

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def reversePoint : Formula := .imp (.member 1 3) (.ex 2 (witness 2))
def basePreimage (target source : Nat) : Formula := namedBoth (.member 0 source)
  (namedBoth (graphFormula 6 source target)
    (.all 4 (.imp (namedBoth (.member 0 4) (graphFormula 6 4 target)) (.equal 4 source))))

private def majorBaseFrame : Formula := .imp bijectionFormula
  (.imp (.member 1 33) (.ex 30 (basePreimage 33 30)))

private def minorBaseFrame : Formula := .imp bijectionFormula
  (.imp (.member 1 34) (.ex 31 (basePreimage 34 31)))

private def backward_clause : KDerivation (imp bijectionFormula.encode (allCode 3 reversePoint.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  have hb : Context [bijectionFormula.encode] bijectionFormula.encode := .head _ _
  change Context [bijectionFormula.encode] (both _ (allCode 3 reversePoint.encode)) at hb
  exact Context.conjunctionRight hb

private def major_base : KDerivation majorBaseFrame.encode := by
  have hi := universalInstance 3 33 reversePoint (by decide) (by decide) (by decide)
  have hs : replace 3 33 reversePoint = .imp (.member 1 33) (.ex 2 (basePreimage 33 2)) := by decide
  rw [hs] at hi
  have ha := (existentialAlpha 2 30 (basePreimage 33 2) (by decide) (by decide) (by decide)).1
  have he : replace 2 30 (basePreimage 33 2) = basePreimage 33 30 := by decide
  rw [he] at ha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 1 33,bijectionFormula.encode]
  have hx : Context Γ (member 1 33) := .head _ _
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hw := Context.mp hx (Context.mp (Context.mp hb (.closed backward_clause)) (.closed hi))
  simpa [majorBaseFrame, Formula.encode] using Context.mp hw (.closed ha)

private def minor_base : KDerivation minorBaseFrame.encode := by
  have hi := universalInstance 3 34 reversePoint (by decide) (by decide) (by decide)
  have hs : replace 3 34 reversePoint = .imp (.member 1 34) (.ex 2 (basePreimage 34 2)) := by decide
  rw [hs] at hi
  have ha := (existentialAlpha 2 31 (basePreimage 34 2) (by decide) (by decide) (by decide)).1
  have he : replace 2 31 (basePreimage 34 2) = basePreimage 34 31 := by decide
  rw [he] at ha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 1 34,bijectionFormula.encode]
  have hx : Context Γ (member 1 34) := .head _ _
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hw := Context.mp hx (Context.mp (Context.mp hb (.closed backward_clause)) (.closed hi))
  simpa [minorBaseFrame, Formula.encode] using Context.mp hw (.closed ha)

def majorPreimage : Formula := namedBoth (.member 0 30)
  (namedBoth (graphFormula 40 30 33) (.all 4 (.imp
    (namedBoth (.member 0 4) (graphFormula 40 4 33)) (.equal 4 30))))

def minorPreimage : Formula := namedBoth (.member 1 31)
  (namedBoth (graphFormula 41 31 34) (.all 4 (.imp
    (namedBoth (.member 1 4) (graphFormula 41 4 34)) (.equal 4 31))))

def majorFrame : Formula := replace 1 42 (replace 6 40 majorBaseFrame)
def minorFrame : Formula := replace 0 1 (replace 1 43 (replace 6 41 minorBaseFrame))

theorem major_frame_shape : majorFrame = .imp firstBijection
    (.imp (.member 42 33) (.ex 30 majorPreimage)) := by decide
theorem minor_frame_shape : minorFrame = .imp secondBijection
    (.imp (.member 43 34) (.ex 31 minorPreimage)) := by decide

/-- Choose the major source preimage of target coordinate 33. -/
def major_preimage : KDerivation (imp firstBijection.encode
    (imp (member 42 33) (existsCode 30 majorPreimage.encode))) := by
  have h1 := replace_derivation 6 40 majorBaseFrame (by decide) (by decide) major_base
  have h2 := replace_derivation 1 42 (replace 6 40 majorBaseFrame) (by decide) (by decide) h1
  change KDerivation majorFrame.encode at h2
  rw [major_frame_shape] at h2
  simpa [Formula.encode] using h2

/-- Choose the minor source preimage of target coordinate 34. -/
def minor_preimage : KDerivation (imp secondBijection.encode
    (imp (member 43 34) (existsCode 31 minorPreimage.encode))) := by
  have h1 := replace_derivation 6 41 minorBaseFrame (by decide) (by decide) minor_base
  have h2 := replace_derivation 1 43 (replace 6 41 minorBaseFrame) (by decide) (by decide) h1
  have h3 := replace_derivation 0 1 (replace 1 43 (replace 6 41 minorBaseFrame))
    (by decide) (by decide) h2
  change KDerivation minorFrame.encode at h3
  rw [minor_frame_shape] at h3
  simpa [Formula.encode] using h3

theorem major_preimage_certificate : theoremCode (certificate major_preimage) =
    imp firstBijection.encode (imp (member 42 33) (existsCode 30 majorPreimage.encode)) := certificate_correct _
theorem minor_preimage_certificate : theoremCode (certificate minor_preimage) =
    imp secondBijection.encode (imp (member 43 34) (existsCode 31 minorPreimage.encode)) := certificate_correct _

end PASoundness.PAtoCompactProductMatchReverseFactors

#print axioms PASoundness.PAtoCompactProductMatchReverseFactors.major_preimage
#print axioms PASoundness.PAtoCompactProductMatchReverseFactors.minor_preimage
#print axioms PASoundness.PAtoCompactProductMatchReverseFactors.major_preimage_certificate
#print axioms PASoundness.PAtoCompactProductMatchReverseFactors.minor_preimage_certificate
