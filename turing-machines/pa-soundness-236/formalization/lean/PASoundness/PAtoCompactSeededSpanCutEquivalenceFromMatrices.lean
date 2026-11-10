import PASoundness.PAtoCompactCommonSourceSpanEquivalence
import PASoundness.PAtoCompactSeededSpanCleanSeedWitness
import PASoundness.PAtoCompactScopedActiveReplace

/-! Two supplied isomorphism matrices from one candidate source to the two
cuts yield the cut-to-cut equivalence used by the clean seed construction. -/
namespace PASoundness.PAtoCompactSeededSpanCutEquivalenceFromMatrices

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactPartialCompositionAtSource PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactCommonSourceSpanInputMatrices PASoundness.PAtoCompactCommonSourceSpanMatrix
open PASoundness.PAtoCompactCommonSourceSpanEquivalence PASoundness.PAtoCompactSeededSpanCleanSeedWitness
open PASoundness.PAtoCompactConditionalTransitivityMatrix

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def firstCutMatrix : Formula := replace 6 46 (replace 1 40 (replace 0 28 sourceMatrix))
def secondCutMatrix : Formula := replace 6 47 (replace 1 41 (replace 0 28 sourceMatrix))

private def frame : Formula := .imp firstMatrix14 (.imp PASoundness.PAtoCompactCommonSourceSpanInputMatrices.secondMatrix
  (.imp (namedCandidate 1) targetEquivalent))
private def f40 : Formula := replace 0 40 frame
private def f41 : Formula := replace 8 41 f40
private def f28 : Formula := replace 1 28 f41
private def f46 : Formula := replace 14 46 f28

/-- Both actual graph witnesses remain explicit; the represented sets may
coincide. -/
def cut_equivalence_from_matrices : KDerivation (imp firstCutMatrix.encode
    (imp secondCutMatrix.encode (imp (namedCandidate 28).encode seedEquivalence.encode))) := by
  have hbase : KDerivation frame.encode := by
    simpa only [frame, Formula.encode] using common_source_images_equivalent
  have h40 := replace_derivation 0 40 frame (by decide) (by decide) hbase
  have h41 := replace_derivation 8 41 f40 (by decide) (by decide) (by simpa only [f40] using h40)
  have h28 := replace_derivation 1 28 f41 (by decide) (by decide) (by simpa only [f41] using h41)
  have h46 := replace_derivation 14 46 f28 (by decide) (by decide) (by simpa only [f28] using h28)
  have h47 := replace_derivation 7 47 f46 (by decide) (by decide) (by simpa only [f46] using h46)
  have halign : replace 7 47 f46 = .imp firstCutMatrix (.imp secondCutMatrix
      (.imp (namedCandidate 28) seedEquivalence)) := by decide
  rw [halign] at h47
  exact h47

theorem cut_equivalence_from_matrices_certificate : theoremCode (certificate cut_equivalence_from_matrices) =
    imp firstCutMatrix.encode (imp secondCutMatrix.encode
      (imp (namedCandidate 28).encode seedEquivalence.encode)) := certificate_correct cut_equivalence_from_matrices

end PASoundness.PAtoCompactSeededSpanCutEquivalenceFromMatrices

#print axioms PASoundness.PAtoCompactSeededSpanCutEquivalenceFromMatrices.firstCutMatrix
#print axioms PASoundness.PAtoCompactSeededSpanCutEquivalenceFromMatrices.secondCutMatrix
#print axioms PASoundness.PAtoCompactSeededSpanCutEquivalenceFromMatrices.cut_equivalence_from_matrices
#print axioms PASoundness.PAtoCompactSeededSpanCutEquivalenceFromMatrices.cut_equivalence_from_matrices_certificate
