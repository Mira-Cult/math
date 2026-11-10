import PASoundness.PAtoCompactProductMatchTargetWitnessFromEdge
import PASoundness.PAtoCompactProductMatchPointWitness
import PASoundness.PAtoCompactScopedActiveReplace

/-! Reuse the guarded product-forward witness at source factor/output labels.
The matrix, both factor memberships, output membership and triple stay explicit. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchSourceForwardWitness

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactProductMatchPointWitness PASoundness.PAtoCompactProductMatchTargetOutput
open PASoundness.PAtoCompactProductMatchTargetWitnessFromEdge

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def targetFrame : Formula := .imp targetMatrix (.imp (.member 42 33) (.imp (.member 43 34)
  (.imp (.member 44 55) (.imp (targetTriple 33 34 55) target55))))
def sourceFrame : Formula := .imp productMatrix (.imp (.member 0 30) (.imp (.member 1 31)
  (.imp (.member 2 32) (.imp (tripleFormula 30 31 32) selectedForwardBody))))

theorem source_frame_shape : replace 55 32 (replace 34 31 (replace 33 30 (replace 44 2
    (replace 43 1 (replace 42 0 (replace 45 6 targetFrame)))))) = sourceFrame := by decide

def source_forward_witness : KDerivation (imp productMatrix.encode (imp (member 0 30)
    (imp (member 1 31) (imp (member 2 32)
      (imp (tripleFormula 30 31 32).encode selectedForwardBody.encode))))) := by
  have h0 : KDerivation targetFrame.encode := by simpa [targetFrame, Formula.encode] using target_witness
  have h1 := replace_derivation 45 6 targetFrame (by decide) (by decide) h0
  have h2 := replace_derivation 42 0 (replace 45 6 targetFrame) (by decide) (by decide) h1
  have h3 := replace_derivation 43 1 (replace 42 0 (replace 45 6 targetFrame)) (by decide) (by decide) h2
  have h4 := replace_derivation 44 2 (replace 43 1 (replace 42 0 (replace 45 6 targetFrame))) (by decide) (by decide) h3
  have h5 := replace_derivation 33 30 (replace 44 2 (replace 43 1 (replace 42 0 (replace 45 6 targetFrame)))) (by decide) (by decide) h4
  have h6 := replace_derivation 34 31 (replace 33 30 (replace 44 2 (replace 43 1 (replace 42 0 (replace 45 6 targetFrame))))) (by decide) (by decide) h5
  have h7 := replace_derivation 55 32 (replace 34 31 (replace 33 30 (replace 44 2 (replace 43 1 (replace 42 0 (replace 45 6 targetFrame)))))) (by decide) (by decide) h6
  rw [source_frame_shape] at h7
  simpa [sourceFrame, Formula.encode] using h7

theorem source_forward_witness_certificate : theoremCode (certificate source_forward_witness) =
    imp productMatrix.encode (imp (member 0 30) (imp (member 1 31) (imp (member 2 32)
      (imp (tripleFormula 30 31 32).encode selectedForwardBody.encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchSourceForwardWitness

#print axioms PASoundness.PAtoCompactProductMatchSourceForwardWitness.source_forward_witness
#print axioms PASoundness.PAtoCompactProductMatchSourceForwardWitness.source_forward_witness_certificate
