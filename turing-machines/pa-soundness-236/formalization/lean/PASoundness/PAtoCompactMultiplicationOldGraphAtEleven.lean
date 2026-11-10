import PASoundness.PAtoCompactMultiplicationOldGraphPreserve

/-! Capture-safe specialization of original-graph inclusion preservation to
new graph name 11, matching the represented row step. It does not establish
new-row coverage, graph existence, or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationOldGraphAtEleven
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactMultiplicationOldGraphPreserve
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- If graph 11 is graph 7 with point 13 adjoined, original graph 10 remains
included in it whenever it was included in graph 7. -/
def old_preserved_at_eleven : KDerivation (imp (namedAdjoin 7 13 11 14).encode
    (imp (oldPreserved 7).encode (oldPreserved 11).encode)) := by
  let f : Formula := .imp extension (.imp (oldPreserved 7) (oldPreserved 12))
  have hc : KDerivation f.encode := old_preserved_step
  have hi := universalInstance 12 11 f (by decide) (by decide) (by decide)
  have h := KDerivation.mp (.generalize 12 hc) hi
  have he : replace 12 11 f = .imp (namedAdjoin 7 13 11 14)
      (.imp (oldPreserved 7) (oldPreserved 11)) := by decide
  rw [he] at h
  exact h

theorem old_preserved_at_eleven_certificate : theoremCode (certificate old_preserved_at_eleven) =
    imp (namedAdjoin 7 13 11 14).encode
      (imp (oldPreserved 7).encode (oldPreserved 11).encode) :=
  certificate_correct old_preserved_at_eleven
end PASoundness.PAtoCompactMultiplicationOldGraphAtEleven
#print axioms PASoundness.PAtoCompactMultiplicationOldGraphAtEleven.old_preserved_at_eleven
#print axioms PASoundness.PAtoCompactMultiplicationOldGraphAtEleven.old_preserved_at_eleven_certificate
