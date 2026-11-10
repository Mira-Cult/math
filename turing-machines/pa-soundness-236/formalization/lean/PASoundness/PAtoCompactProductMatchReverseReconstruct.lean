import PASoundness.PAtoCompactProductMatchReverseProduct
import PASoundness.PAtoCompactProductMatchReverseFactors
import PASoundness.PAtoCompactProductMatchForwardWitnessFromEdge
import PASoundness.PAtoCompactProductMatchTargetWitnessFromEdge
import PASoundness.PAtoCompactProductMatchSourceWitnessFromEdge

/-! Pointwise alignment of reverse-selected product/factor witnesses with
the existing forward matching-path body. All graph matrices, endpoint
membership and reverse-selected witness bodies remain literal antecedents.
This module does not eliminate those witnesses or establish reverse totality. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchReverseReconstruct

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductMatchPointWitness
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductMatchTargetOutput
open PASoundness.PAtoCompactProductMatchSourceWitness PASoundness.PAtoCompactProductMatchReverseProduct
open PASoundness.PAtoCompactProductMatchReverseFactors PASoundness.PAtoCompactProductMatchForwardWitnessFromEdge
open PASoundness.PAtoCompactProductMatchTargetWitnessFromEdge PASoundness.PAtoCompactProductMatchSourceWitnessFromEdge

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceGuard : Formula := namedBoth productMatrix (namedBoth firstBijection
  (namedBoth secondBijection (namedBoth targetMatrix (.member 44 55))))

def reversePack : Formula := namedBoth targetReverseBody (namedBoth majorPreimage
  (namedBoth minorPreimage selectedForwardBody))

def pathBody55 : Formula := replace 35 55 retainedMatchBody

theorem target_reverse_shape : targetReverseBody = namedBoth (.member 42 33)
    (namedBoth (.member 43 34) (namedBoth (targetTriple 33 34 55)
      (.all 7 (.all 8 (.imp (namedBoth (.member 42 7) (namedBoth (.member 43 8)
        (targetTriple 7 8 55))) (namedBoth (.equal 7 33) (.equal 8 34))))))) := by decide

theorem path_body_shape : pathBody55 = namedBoth selectedReverseBody
    (namedBoth (namedBoth firstImage secondImage) target55) := by decide

/-- Reconstruct every forward-path witness clause from the displayed
reverse witnesses and the four supplied matrices. -/
def reconstruct : KDerivation (imp sourceGuard.encode (imp reversePack.encode pathBody55.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [reversePack.encode,sourceGuard.encode]
  have hr : Context Γ reversePack.encode := .head _ _
  have hg : Context Γ sourceGuard.encode := .hypothesis (by simp [Γ])
  have hr' : Context Γ (both targetReverseBody.encode (both majorPreimage.encode
      (both minorPreimage.encode selectedForwardBody.encode))) := by
    simpa [reversePack, namedBoth, Formula.not, Formula.encode, both, neg] using hr
  have hg' : Context Γ (both productMatrix.encode (both firstBijection.encode
      (both secondBijection.encode (both targetMatrix.encode (member 44 55))))) := by
    simpa [sourceGuard, namedBoth, Formula.not, Formula.encode, both, neg] using hg
  have htr := Context.conjunctionLeft hr'
  have hmajor := Context.conjunctionLeft (Context.conjunctionRight hr')
  have hminor := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hr'))
  have hsf := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hr'))
  have hp := Context.conjunctionLeft hg'
  have hb₁ := Context.conjunctionLeft (Context.conjunctionRight hg')
  have hb₂ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hg'))
  have ht := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg')))
  have hz := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg')))
  have htr' : Context Γ (both (member 42 33) (both (member 43 34)
      (both (targetTriple 33 34 55).encode
        (Formula.all 7 (.all 8 (.imp (namedBoth (.member 42 7) (namedBoth (.member 43 8)
          (targetTriple 7 8 55))) (namedBoth (.equal 7 33) (.equal 8 34))))).encode))) := by
    simpa [target_reverse_shape, namedBoth, Formula.not, Formula.encode, both, neg] using htr
  have hmajor' : Context Γ (both (member 0 30) (both (graphFormula 40 30 33).encode
      (Formula.all 4 (.imp (namedBoth (.member 0 4) (graphFormula 40 4 33)) (.equal 4 30))).encode)) := by
    simpa [majorPreimage, namedBoth, Formula.not, Formula.encode, both, neg] using hmajor
  have hminor' : Context Γ (both (member 1 31) (both (graphFormula 41 31 34).encode
      (Formula.all 4 (.imp (namedBoth (.member 1 4) (graphFormula 41 4 34)) (.equal 4 31))).encode)) := by
    simpa [minorPreimage, namedBoth, Formula.not, Formula.encode, both, neg] using hminor
  have hsf' : Context Γ (both (member 2 32) (both (tripleFormula 30 31 32).encode
      (Formula.all 9 PAtoCompactProductMatchPointUnique.forwardUnique).encode)) := by
    simpa [PAtoCompactProductMatchPointUnique.forward_selected_shape,
      namedBoth, Formula.not, Formula.encode, both, neg] using hsf
  have hx := Context.conjunctionLeft hmajor'
  have hy := Context.conjunctionLeft hminor'
  have ha := Context.conjunctionLeft htr'
  have hb := Context.conjunctionLeft (Context.conjunctionRight htr')
  have hsourceOut := Context.conjunctionLeft hsf'
  have hsourceTriple := Context.conjunctionLeft (Context.conjunctionRight hsf')
  have htargetTriple := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight htr'))
  have hmajorEdge := Context.conjunctionLeft (Context.conjunctionRight hmajor')
  have hminorEdge := Context.conjunctionLeft (Context.conjunctionRight hminor')
  have hR : Context Γ selectedReverseBody.encode :=
    .mp hsourceTriple (.mp hsourceOut (.mp hy (.mp hx (.mp hp (.closed source_witness)))))
  have hF : Context Γ firstImage.encode := .mp hmajorEdge (.mp ha (.mp hx (.mp hb₁ (.closed major_witness))))
  have hS : Context Γ secondImage.encode := .mp hminorEdge (.mp hb (.mp hy (.mp hb₂ (.closed minor_witness))))
  have hT : Context Γ target55.encode := .mp htargetTriple (.mp hz (.mp hb (.mp ha (.mp ht (.closed target_witness)))))
  have h := Context.conjunctionIntro hR (Context.conjunctionIntro (Context.conjunctionIntro hF hS) hT)
  simpa [path_body_shape, namedBoth, Formula.not, Formula.encode, both, neg] using h

theorem reconstruct_certificate : theoremCode (certificate reconstruct) =
    imp sourceGuard.encode (imp reversePack.encode pathBody55.encode) := certificate_correct _

end PASoundness.PAtoCompactProductMatchReverseReconstruct

#print axioms PASoundness.PAtoCompactProductMatchReverseReconstruct.reconstruct
#print axioms PASoundness.PAtoCompactProductMatchReverseReconstruct.reconstruct_certificate
