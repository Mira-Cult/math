import PASoundness.PAtoCompactProductMatchReversePreimages

/-! Construct a reverse product-match path after target-product coordinates
have been selected. All graph-matrix and target-member assumptions remain
explicit; this does not yet eliminate those target-coordinate witnesses. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchReverseAtCoordinates

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactProductMatchPointWitness
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductMatchReverseProduct
open PASoundness.PAtoCompactProductMatchTargetOutput
open PASoundness.PAtoCompactProductMatchReverseFactors PASoundness.PAtoCompactProductMatchReverseReconstruct
open PASoundness.PAtoCompactProductMatchReversePreimages

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def preimagePack : Formula := namedBoth targetReverseBody (namedBoth majorPreimage minorPreimage)

/-- Select a source-product output while retaining the chosen target
coordinates and both source-factor preimage witnesses. -/
def source_output : KDerivation
    (imp productMatrix.encode (imp preimagePack.encode (existsCode 32 reversePack.encode))) := by
  have hpoint : KDerivation (imp preimagePack.encode (imp selectedForwardBody.encode reversePack.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [selectedForwardBody.encode,preimagePack.encode]
    have hf : Context Γ selectedForwardBody.encode := .head _ _
    have hp : Context Γ preimagePack.encode := .hypothesis (by simp [Γ])
    have hp' : Context Γ (both targetReverseBody.encode (both majorPreimage.encode minorPreimage.encode)) := by
      simpa [preimagePack, namedBoth, Formula.not, Formula.encode, both, neg] using hp
    have ht := Context.conjunctionLeft hp'
    have hm := Context.conjunctionLeft (Context.conjunctionRight hp')
    have hn := Context.conjunctionRight (Context.conjunctionRight hp')
    have h := Context.conjunctionIntro ht (Context.conjunctionIntro hm (Context.conjunctionIntro hn hf))
    simpa [reversePack, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hpack := conditionalExistsCongr 32 (preimagePack.vacuity 32 (by decide)) hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [preimagePack.encode,productMatrix.encode]
  have hp : Context Γ preimagePack.encode := .head _ _
  have hm : Context Γ productMatrix.encode := .hypothesis (by simp [Γ])
  have hp' : Context Γ (both targetReverseBody.encode (both majorPreimage.encode minorPreimage.encode)) := by
    simpa [preimagePack, namedBoth, Formula.not, Formula.encode, both, neg] using hp
  have hmajor := Context.conjunctionLeft (Context.conjunctionRight hp')
  have hminor := Context.conjunctionRight (Context.conjunctionRight hp')
  have hmajor' : Context Γ (both (member 0 30) (both (PAtoCompactOrderIsomorphism.graphFormula 40 30 33).encode
      (Formula.all 4 (.imp (namedBoth (.member 0 4)
        (PAtoCompactOrderIsomorphism.graphFormula 40 4 33)) (.equal 4 30))).encode)) := by
    simpa [majorPreimage, namedBoth, Formula.not, Formula.encode, both, neg] using hmajor
  have hminor' : Context Γ (both (member 1 31) (both (PAtoCompactOrderIsomorphism.graphFormula 41 31 34).encode
      (Formula.all 4 (.imp (namedBoth (.member 1 4)
        (PAtoCompactOrderIsomorphism.graphFormula 41 4 34)) (.equal 4 31))).encode)) := by
    simpa [minorPreimage, namedBoth, Formula.not, Formula.encode, both, neg] using hminor
  have hx := Context.conjunctionLeft hmajor'
  have hy := Context.conjunctionLeft hminor'
  have hf : Context Γ (existsCode 32 selectedForwardBody.encode) := .mp hy (.mp hx (.mp hm (.closed forward_output)))
  exact .mp hf (.mp hp (.closed hpack))

/-- Assuming the target coordinates are already selected, construct a
source output and a full forward-path body at target output 55. -/
def path_at_coordinates : KDerivation
    (imp sourceGuard.encode (imp targetReverseBody.encode
      (existsCode 30 (existsCode 31 (existsCode 32 pathBody55.encode))))) := by
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
  have halign₃₂ := conditionalExistsCongr 32 (sourceGuard.vacuity 32 (by decide)) reconstruct
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

theorem path_at_coordinates_certificate : theoremCode (certificate path_at_coordinates) =
    imp sourceGuard.encode (imp targetReverseBody.encode
      (existsCode 30 (existsCode 31 (existsCode 32 pathBody55.encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchReverseAtCoordinates

#print axioms PASoundness.PAtoCompactProductMatchReverseAtCoordinates.source_output
#print axioms PASoundness.PAtoCompactProductMatchReverseAtCoordinates.path_at_coordinates
#print axioms PASoundness.PAtoCompactProductMatchReverseAtCoordinates.path_at_coordinates_certificate
