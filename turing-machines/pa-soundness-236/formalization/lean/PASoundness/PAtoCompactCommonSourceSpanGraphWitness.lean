import PASoundness.PAtoCompactCommonSourceSpanMatrix

/-! Construct the common-source span graph at the allocation needed by the
restricted inverse/matrix transfer: first input graph 14, second graph 7,
output graph 9. The common-source candidate and both input matrices remain
explicit hypotheses; no candidate assumption is made for the image objects. -/
namespace PASoundness.PAtoCompactCommonSourceSpanGraphWitness

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactPartialCompositionAtSource PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactCommonSourceSpanBase PASoundness.PAtoCompactCommonSourceSpanInputMatrices
open PASoundness.PAtoCompactCommonSourceSpanComposition PASoundness.PAtoCompactCommonSourceSpanMatrix

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def sourceFrame : Formula := .imp firstMatrix (.imp secondMatrix
  (.imp (namedCandidate 1) (.ex 9 (replace 10 1 spanComposition))))
private def movedFrame : Formula := replace 6 14 sourceFrame

private theorem source_frame_code : sourceFrame.encode =
    imp firstMatrix.encode (imp secondMatrix.encode (imp (namedCandidate 1).encode
      (existsCode 9 (replace 10 1 spanComposition).encode))) := rfl

private theorem moved_frame_alignment : movedFrame =
    .imp firstMatrix14 (.imp secondMatrix (.imp (namedCandidate 1) (.ex 9 spanFull))) := by decide

/-- Actual common-source span graph from both input matrices and common
candidate, capture-safely rebased away from inverse graph name 6. -/
def span_graph_exists : KDerivation (imp firstMatrix14.encode (imp secondMatrix.encode
    (imp (namedCandidate 1).encode (existsCode 9 spanFull.encode)))) := by
  have hs : KDerivation sourceFrame.encode := by
    rw [source_frame_code]
    exact span_from_input_matrices
  have hm := replace_derivation 6 14 sourceFrame (by decide) (by decide) hs
  have hf : KDerivation movedFrame.encode := by simpa only [movedFrame] using hm
  rw [moved_frame_alignment] at hf
  exact hf

theorem span_graph_exists_certificate : theoremCode (certificate span_graph_exists) =
    imp firstMatrix14.encode (imp secondMatrix.encode
      (imp (namedCandidate 1).encode (existsCode 9 spanFull.encode))) :=
  certificate_correct span_graph_exists

end PASoundness.PAtoCompactCommonSourceSpanGraphWitness

#print axioms PASoundness.PAtoCompactCommonSourceSpanGraphWitness.span_graph_exists
#print axioms PASoundness.PAtoCompactCommonSourceSpanGraphWitness.span_graph_exists_certificate
