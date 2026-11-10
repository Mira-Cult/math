import PASoundness.PAtoCompactProductMatchReverseReconstruct
import PASoundness.PAtoCompactProductMatchPointUnique

/-! Preserve the source-product membership selected by reverse matching.
This is a pointwise constructor; existential witnesses and graph coverage
remain to be assembled. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchReverseRetainedSource

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductMatchPointWitness PASoundness.PAtoCompactProductMatchPointUnique
open PASoundness.PAtoCompactProductMatchReverseProduct PASoundness.PAtoCompactProductMatchReverseFactors
open PASoundness.PAtoCompactProductMatchReverseReconstruct

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def retainedSourceBody : Formula := namedBoth (.member 2 32) pathBody55

/-- Keep the source member and matching body on the same selected output. -/
def reconstruct_retaining_source : KDerivation
    (imp sourceGuard.encode (imp reversePack.encode retainedSourceBody.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [reversePack.encode, sourceGuard.encode]
  have hr : Context Γ reversePack.encode := .head _ _
  have hg : Context Γ sourceGuard.encode := .hypothesis (by simp [Γ])
  have hr' : Context Γ (both targetReverseBody.encode (both majorPreimage.encode
      (both minorPreimage.encode selectedForwardBody.encode))) := by
    simpa [reversePack, namedBoth, Formula.not, Formula.encode, both, neg] using hr
  have hf := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hr'))
  have hf' : Context Γ (both (member 2 32) (both (tripleFormula 30 31 32).encode
      (Formula.all 9 forwardUnique).encode)) := by
    simpa [forward_selected_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hf
  have hm := Context.conjunctionLeft hf'
  have hp := Context.mp hr (Context.mp hg (.closed reconstruct))
  have h := Context.conjunctionIntro hm hp
  simpa [Γ, retainedSourceBody, namedBoth, Formula.not, Formula.encode, both, neg] using h

theorem reconstruct_retaining_source_certificate :
    theoremCode (certificate reconstruct_retaining_source) =
      imp sourceGuard.encode (imp reversePack.encode retainedSourceBody.encode) :=
  certificate_correct _

end PASoundness.PAtoCompactProductMatchReverseRetainedSource

#print axioms PASoundness.PAtoCompactProductMatchReverseRetainedSource.reconstruct_retaining_source
#print axioms PASoundness.PAtoCompactProductMatchReverseRetainedSource.reconstruct_retaining_source_certificate
