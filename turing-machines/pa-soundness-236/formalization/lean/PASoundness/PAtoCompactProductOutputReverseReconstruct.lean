import PASoundness.PAtoCompactProductOutputImageFromEdge
import PASoundness.PAtoCompactProductOutputPreimagePoint
import PASoundness.PAtoCompactProductOutputForwardFromReverse

/-! Reconstruct the actual forward path body from a selected target preimage
and source-product reverse coordinates, retaining the same source output,
coordinates and target output. Matrix/bijection and target membership remain
explicit; no graph collection is inferred here. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputReverseReconstruct

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductOutputImagePoint
open PASoundness.PAtoCompactProductOutputPreimagePoint PASoundness.PAtoCompactProductOutputForwardFromReverse
open PASoundness.PAtoCompactProductOutputImageFromEdge

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def reconstructed : Formula := namedBoth preimage32
  (namedBoth reverseBody PAtoCompactProductOutputImagePoint.pairedBody)

def reconstruct : KDerivation (imp sourceMatrix.encode (imp firstBijection.encode
    (imp (member 42 33) (imp PAtoCompactProductOutputPreimagePoint.pairedBody.encode reconstructed.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [PAtoCompactProductOutputPreimagePoint.pairedBody.encode,member 42 33,
    firstBijection.encode,sourceMatrix.encode]
  have hp : Context Γ PAtoCompactProductOutputPreimagePoint.pairedBody.encode := .head _ _
  have hy : Context Γ (member 42 33) := .hypothesis (by simp [Γ])
  have hb : Context Γ firstBijection.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ sourceMatrix.encode := .hypothesis (by simp [Γ])
  have hp' : Context Γ (both preimage32.encode reverseBody.encode) := by
    simpa [PAtoCompactProductOutputPreimagePoint.pairedBody, namedBoth,
      CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hp
  have hpre : Context Γ (both (member 0 32) (both (graphFormula 40 32 33).encode
      (Formula.all 4 (.imp (namedBoth (.member 0 4) (graphFormula 40 4 33)) (.equal 4 32))).encode)) := by
    simpa [preimage_shape, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using Context.conjunctionLeft hp'
  have hsource := Context.mp (Context.conjunctionRight hp')
    (Context.mp (Context.conjunctionLeft hpre) (Context.mp hm (.closed forward_from_reverse)))
  have himage := Context.mp (Context.conjunctionLeft (Context.conjunctionRight hpre))
    (Context.mp hy (Context.mp (Context.conjunctionLeft hpre) (Context.mp hb (.closed image_from_edge))))
  have hpair : Context Γ PAtoCompactProductOutputImagePoint.pairedBody.encode := by
    simpa [PAtoCompactProductOutputImagePoint.pairedBody, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using Context.conjunctionIntro hsource himage
  simpa [reconstructed, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
    Context.conjunctionIntro (Context.conjunctionLeft hp')
      (Context.conjunctionIntro (Context.conjunctionRight hp') hpair)

theorem reconstruct_certificate : theoremCode (certificate reconstruct) =
    imp sourceMatrix.encode (imp firstBijection.encode (imp (member 42 33)
      (imp PAtoCompactProductOutputPreimagePoint.pairedBody.encode reconstructed.encode))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputReverseReconstruct

#print axioms PASoundness.PAtoCompactProductOutputReverseReconstruct.reconstruct
#print axioms PASoundness.PAtoCompactProductOutputReverseReconstruct.reconstruct_certificate
