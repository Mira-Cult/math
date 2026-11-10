import PASoundness.PAtoCompactProductMatchReverseAtCoordinates
import PASoundness.PAtoCompactProductMatchReverseRetainedSource

/-! Reverse matching at chosen target coordinates, retaining the source
membership on the same source output as the path body. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchReverseAtCoordinatesRetained

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactProductMatchPointWitness
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductMatchReverseProduct
open PASoundness.PAtoCompactProductMatchTargetOutput
open PASoundness.PAtoCompactProductMatchReverseFactors PASoundness.PAtoCompactProductMatchReverseReconstruct
open PASoundness.PAtoCompactProductMatchReversePreimages PASoundness.PAtoCompactProductMatchReverseAtCoordinates
open PASoundness.PAtoCompactProductMatchReverseRetainedSource

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def path_at_coordinates_retaining_source : KDerivation
    (imp sourceGuard.encode (imp targetReverseBody.encode
      (existsCode 30 (existsCode 31 (existsCode 32 retainedSourceBody.encode))))) := by
  have hretain : KDerivation (imp targetReverseBody.encode (imp bothPreimages.encode preimagePack.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [bothPreimages.encode,targetReverseBody.encode]
    have hp : Context Γ bothPreimages.encode := .head _ _
    have ht : Context Γ targetReverseBody.encode := .hypothesis (by simp [Γ])
    have hp' : Context Γ (both majorPreimage.encode minorPreimage.encode) := by
      simpa [bothPreimages, namedBoth, Formula.not, Formula.encode, both, neg] using hp
    have h := Context.conjunctionIntro ht hp'
    simpa [preimagePack, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hretain₃₁ := conditionalExistsCongr 31 (targetReverseBody.vacuity 31 (by decide)) hretain
  have hretain₃₀ := conditionalExistsCongr 30 (targetReverseBody.vacuity 30 (by decide)) hretain₃₁
  have hsourcePoint : KDerivation (imp sourceGuard.encode
      (imp preimagePack.encode (existsCode 32 reversePack.encode))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [preimagePack.encode,sourceGuard.encode]
    have hp : Context Γ preimagePack.encode := .head _ _
    have hg : Context Γ sourceGuard.encode := .hypothesis (by simp [Γ])
    have hg' : Context Γ (both productMatrix.encode (both firstBijection.encode
        (both secondBijection.encode (both targetMatrix.encode (member 44 55))))) := by
      simpa [sourceGuard, namedBoth, Formula.not, Formula.encode, both, neg] using hg
    exact .mp hp (.mp (Context.conjunctionLeft hg') (.closed source_output))
  have hsource₃₁ := conditionalExistsCongr 31 (sourceGuard.vacuity 31 (by decide)) hsourcePoint
  have hsource₃₀ := conditionalExistsCongr 30 (sourceGuard.vacuity 30 (by decide)) hsource₃₁
  have halign₃₂ := conditionalExistsCongr 32 (sourceGuard.vacuity 32 (by decide)) reconstruct_retaining_source
  have halign₃₁ := conditionalExistsCongr 31 (sourceGuard.vacuity 31 (by decide)) halign₃₂
  have halign₃₀ := conditionalExistsCongr 30 (sourceGuard.vacuity 30 (by decide)) halign₃₁
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [targetReverseBody.encode,sourceGuard.encode]
  have ht : Context Γ targetReverseBody.encode := .head _ _
  have hg : Context Γ sourceGuard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both productMatrix.encode (both firstBijection.encode
      (both secondBijection.encode (both targetMatrix.encode (member 44 55))))) := by
    simpa [sourceGuard, namedBoth, Formula.not, Formula.encode, both, neg] using hg
  have hb₁ := Context.conjunctionLeft (Context.conjunctionRight hg')
  have hb₂ := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hg'))
  have hp : Context Γ (existsCode 30 (existsCode 31 bothPreimages.encode)) :=
    .mp hb₂ (.mp hb₁ (.mp ht (.closed both_preimages)))
  have hp' := Context.mp hp (Context.mp ht (.closed hretain₃₀))
  have hr := Context.mp hp' (Context.mp hg (.closed hsource₃₀))
  exact .mp hr (.mp hg (.closed halign₃₀))


theorem path_at_coordinates_retaining_source_certificate :
    theoremCode (certificate path_at_coordinates_retaining_source) =
      imp sourceGuard.encode (imp targetReverseBody.encode
        (existsCode 30 (existsCode 31 (existsCode 32 retainedSourceBody.encode)))) :=
  certificate_correct _

end PASoundness.PAtoCompactProductMatchReverseAtCoordinatesRetained

#print axioms PASoundness.PAtoCompactProductMatchReverseAtCoordinatesRetained.path_at_coordinates_retaining_source
#print axioms PASoundness.PAtoCompactProductMatchReverseAtCoordinatesRetained.path_at_coordinates_retaining_source_certificate
