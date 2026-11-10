import PASoundness.PAtoCompactMultiplicationOldForwardWitnessClosed

/-! The old-major forward witness specialized to the full row prefix, which
is syntactically the same free name as its source domain. The corresponding
K derivation uses capture-safe universal instantiation; it does not construct
a graph or prove the complete product matrix. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationOldForwardWitnessFullPrefix
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactMultiplicationOldForwardSpecialize
open PASoundness.PAtoCompactMultiplicationOldForwardWitnessClosed
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def statement : Formula := .imp hypotheses
  (.imp oldForward (.imp (.member 31 4) (.ex 5 newOutput)))

/-- With prefix 0 identified with source 31, the existing old-major witness
proof transfers to exactly the full-prefix row invariant's no-garbage shape.
All original graph, cut and domain hypotheses are retained. -/
def old_forward_full_prefix : KDerivation (imp (replace 0 31 hypotheses).encode
    (imp oldForward.encode (imp (member 31 4) (existsCode 5 newOutput.encode)))) := by
  have hs : KDerivation statement.encode := old_forward_witness
  have hi := universalInstance 0 31 statement (by decide) (by decide) (by decide)
  have h := KDerivation.mp (.generalize 0 hs) hi
  have hr : replace 0 31 statement = .imp (replace 0 31 hypotheses)
      (.imp oldForward (.imp (.member 31 4) (.ex 5 newOutput))) := by decide
  rw [hr] at h
  exact h

theorem old_forward_full_prefix_certificate : theoremCode (certificate old_forward_full_prefix) =
    imp (replace 0 31 hypotheses).encode
      (imp oldForward.encode (imp (member 31 4) (existsCode 5 newOutput.encode))) :=
  certificate_correct old_forward_full_prefix
end PASoundness.PAtoCompactMultiplicationOldForwardWitnessFullPrefix
#print axioms PASoundness.PAtoCompactMultiplicationOldForwardWitnessFullPrefix.old_forward_full_prefix
#print axioms PASoundness.PAtoCompactMultiplicationOldForwardWitnessFullPrefix.old_forward_full_prefix_certificate
