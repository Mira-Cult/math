import PASoundness.PAtoCompactProductOutputForwardFromReverse
import PASoundness.PAtoCompactFreeVacuity

/-! For a chosen source-product output, select its source coordinates and its
image through the output bijection, retaining the same chosen source output.
This is pointwise existence, not a collected target product graph. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputSourcePoint

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactProductMatchFactorImages
open PASoundness.PAtoCompactProductOutputImagePoint PASoundness.PAtoCompactProductOutputPreimagePoint
open PASoundness.PAtoCompactProductOutputForwardFromReverse

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceGuard : Formula := namedBoth sourceMatrix (namedBoth firstBijection (.member 0 32))
def selectedBody : Formula := namedBoth reverseBody PAtoCompactProductOutputImagePoint.pairedBody

/-- Keep source output 32 and its selected coordinates while choosing their
image output 33. -/
def selected_source_point : KDerivation (imp sourceGuard.encode
    (existsCode 30 (existsCode 31 (existsCode 33
      selectedBody.encode)))) := by
  have hretain : KDerivation (imp reverseBody.encode
      (imp PAtoCompactProductOutputImagePoint.pairedBody.encode selectedBody.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [PAtoCompactProductOutputImagePoint.pairedBody.encode, reverseBody.encode]
    have hp : Context Γ PAtoCompactProductOutputImagePoint.pairedBody.encode := .head _ _
    have hr : Context Γ reverseBody.encode := .hypothesis (by simp [Γ])
    simpa [selectedBody, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode,
      both, neg] using Context.conjunctionIntro hr hp
  have hlift := conditionalExistsCongr 33 (free_vacuity 33 reverseBody (by decide)) hretain
  have hpoint : KDerivation (imp sourceGuard.encode (imp reverseBody.encode
      (existsCode 33 selectedBody.encode))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [reverseBody.encode,sourceGuard.encode]
    have hr : Context Γ reverseBody.encode := .head _ _
    have hg : Context Γ sourceGuard.encode := .hypothesis (by simp [Γ])
    have hg' : Context Γ (both sourceMatrix.encode (both firstBijection.encode (member 0 32))) := by
      simpa [sourceGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode,
        both, neg] using hg
    have hm := Context.conjunctionLeft hg'
    have hb := Context.conjunctionLeft (Context.conjunctionRight hg')
    have ho := Context.conjunctionRight (Context.conjunctionRight hg')
    have hf : Context Γ sourceBody.encode := .mp hr (.mp ho (.mp hm (.closed forward_from_reverse)))
    have hi := Context.mp hf (Context.mp hb (.closed output_image_retained))
    exact .mp hi (.mp hr (.closed hlift))
  have h31 := conditionalExistsCongr 31 (free_vacuity 31 sourceGuard (by decide)) hpoint
  have h30 := conditionalExistsCongr 30 (free_vacuity 30 sourceGuard (by decide)) h31
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [sourceGuard.encode]
  have hg : Context Γ sourceGuard.encode := .head _ _
  have hg' : Context Γ (both sourceMatrix.encode (both firstBijection.encode (member 0 32))) := by
    simpa [sourceGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode,
      both, neg] using hg
  have hm := Context.conjunctionLeft hg'
  have ho := Context.conjunctionRight (Context.conjunctionRight hg')
  have hc := Context.mp ho (Context.mp hm (.closed source_coordinates))
  exact .mp hc (.mp hg (.closed h30))

theorem selected_source_point_certificate : theoremCode (certificate selected_source_point) =
    imp sourceGuard.encode (existsCode 30 (existsCode 31 (existsCode 33
      selectedBody.encode))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputSourcePoint

#print axioms PASoundness.PAtoCompactProductOutputSourcePoint.selected_source_point
#print axioms PASoundness.PAtoCompactProductOutputSourcePoint.selected_source_point_certificate
