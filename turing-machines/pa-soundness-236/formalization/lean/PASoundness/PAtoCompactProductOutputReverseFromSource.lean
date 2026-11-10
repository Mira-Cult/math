import PASoundness.PAtoCompactProductMatchSourceWitnessFromEdge
import PASoundness.PAtoCompactProductOutputReverseCoverage

/-! Recover source-product reverse coordinate uniqueness from a supplied
actual source triple at the same factor coordinates and output. The source
product matrix and all three memberships remain explicit. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputReverseFromSource

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductMatchPointWitness PASoundness.PAtoCompactProductMatchSourceWitnessFromEdge
open PASoundness.PAtoCompactProductOutputReverseCoverage

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceFrame : Formula := .imp productMatrix (.imp (.member 0 30) (.imp (.member 1 31)
  (.imp (.member 2 32) (.imp (tripleFormula 30 31 32) selectedReverseBody))))
def targetFrame : Formula := .imp relocatedMatrix (.imp (.member 43 30) (.imp (.member 44 31)
  (.imp (.member 0 32) (.imp (tripleFormula 30 31 32) relocatedReverse))))

theorem target_frame_shape : replace 2 0 (replace 1 44 (replace 0 43 sourceFrame)) = targetFrame := by decide

def reverse_from_source : KDerivation (imp relocatedMatrix.encode (imp (member 43 30)
    (imp (member 44 31) (imp (member 0 32)
      (imp (tripleFormula 30 31 32).encode relocatedReverse.encode))))) := by
  have h0 : KDerivation sourceFrame.encode := by
    simpa [sourceFrame, CompactNamed.Formula.encode] using source_witness
  have h1 := replace_derivation 0 43 sourceFrame (by decide) (by decide) h0
  have h2 := replace_derivation 1 44 (replace 0 43 sourceFrame) (by decide) (by decide) h1
  have h3 := replace_derivation 2 0 (replace 1 44 (replace 0 43 sourceFrame)) (by decide) (by decide) h2
  rw [target_frame_shape] at h3
  simpa [targetFrame, CompactNamed.Formula.encode] using h3

theorem reverse_from_source_certificate : theoremCode (certificate reverse_from_source) =
    imp relocatedMatrix.encode (imp (member 43 30) (imp (member 44 31)
      (imp (member 0 32) (imp (tripleFormula 30 31 32).encode relocatedReverse.encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputReverseFromSource

#print axioms PASoundness.PAtoCompactProductOutputReverseFromSource.reverse_from_source
#print axioms PASoundness.PAtoCompactProductOutputReverseFromSource.reverse_from_source_certificate
