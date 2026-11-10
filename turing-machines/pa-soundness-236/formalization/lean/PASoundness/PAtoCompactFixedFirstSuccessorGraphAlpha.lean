import PASoundness.PAtoCompactFixedFirstPreservedBase

/-! Alpha-rebind the constructed successor row graph from witness name 11 to
name 7. This is a capture-safe K proof transformation, not graph existence,
row collection, or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstSuccessorGraphAlpha
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactFixedFirstPreservedBase

/-- The two witness names encode the same successor-prefix invariant after
capture-safe replacement; no values are assumed distinct. -/
def alpha_graph_witness : KDerivation
    (imp (existsCode 11 (replace 0 1 (rowInvariantPreserved 11)).encode)
      (existsCode 7 (replace 0 1 (rowInvariantPreserved 7)).encode)) := by
  let f := replace 0 1 (rowInvariantPreserved 11)
  have h := (existentialAlpha 11 7 f (by decide) (by decide) (by decide)).1
  have he : replace 11 7 f = replace 0 1 (rowInvariantPreserved 7) := by decide
  rw [he] at h
  exact h

theorem alpha_graph_witness_certificate : theoremCode (certificate alpha_graph_witness) =
    imp (existsCode 11 (replace 0 1 (rowInvariantPreserved 11)).encode)
      (existsCode 7 (replace 0 1 (rowInvariantPreserved 7)).encode) :=
  certificate_correct alpha_graph_witness
end PASoundness.PAtoCompactFixedFirstSuccessorGraphAlpha
#print axioms PASoundness.PAtoCompactFixedFirstSuccessorGraphAlpha.alpha_graph_witness
#print axioms PASoundness.PAtoCompactFixedFirstSuccessorGraphAlpha.alpha_graph_witness_certificate
