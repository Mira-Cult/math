import PASoundness.PAtoCompactProductMatchForwardWitnessFromEdge
import PASoundness.PAtoCompactProductOutputImagePoint

/-! Recover the full forward image witness of a source product output from an
actual output-bijection edge and its endpoint memberships. No product graph
collection or reverse coverage is asserted. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputImageFromEdge

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductMatchForwardWitnessFromEdge
open PASoundness.PAtoCompactProductOutputImagePoint

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceFrame : Formula := PAtoCompactProductMatchForwardWitnessFromEdge.majorFrame
def targetFrame : Formula := .imp firstBijection (.imp (.member 0 32)
  (.imp (.member 42 33) (.imp (graphFormula 40 32 33) imageBody)))

theorem target_frame_shape : replace 30 32 sourceFrame = targetFrame := by decide

def image_from_edge : KDerivation (imp firstBijection.encode (imp (member 0 32)
    (imp (member 42 33) (imp (graphFormula 40 32 33).encode imageBody.encode)))) := by
  have h0 : KDerivation sourceFrame.encode := by
    simpa [sourceFrame, PAtoCompactProductMatchForwardWitnessFromEdge.majorFrame,
      CompactNamed.Formula.encode] using major_witness
  have h1 := replace_derivation 30 32 sourceFrame (by decide) (by decide) h0
  rw [target_frame_shape] at h1
  simpa [targetFrame, CompactNamed.Formula.encode] using h1

theorem image_from_edge_certificate : theoremCode (certificate image_from_edge) =
    imp firstBijection.encode (imp (member 0 32)
      (imp (member 42 33) (imp (graphFormula 40 32 33).encode imageBody.encode))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputImageFromEdge

#print axioms PASoundness.PAtoCompactProductOutputImageFromEdge.image_from_edge
#print axioms PASoundness.PAtoCompactProductOutputImageFromEdge.image_from_edge_certificate
