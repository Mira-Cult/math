import PASoundness.PAtoCompactMultiplicationCleanOldTripleOutput

/-! Capture-safe specialization of the clean old product output bound to a
fresh competitor label. This assumes an actual clean old graph and triple; it
does not construct a graph or prove product uniqueness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationCleanOldTripleOutput70
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactMultiplicationCleanOldTripleOutput
open PASoundness.PAtoCompactMultiplicationCleanOldMemberOutput
open PASoundness.PAtoCompactMultiplicationOldTripleIntro
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The output at competitor label 70 belongs to the old product result. -/
def old_triple_output70 : KDerivation (imp oldClean.encode
    (imp (replace 5 70 oldTriple).encode (member 32 70))) := by
  let f : Formula := .imp oldClean (.imp oldTriple (.member 32 5))
  have h : KDerivation f.encode := old_triple_output
  have h' := KDerivation.mp (.generalize 5 h)
    (universalInstance 5 70 f (by decide) (by decide) (by decide))
  have hs : replace 5 70 f = .imp oldClean (.imp (replace 5 70 oldTriple) (.member 32 70)) := by decide
  rw [hs] at h'
  exact h'

theorem old_triple_output70_certificate : theoremCode (certificate old_triple_output70) =
    imp oldClean.encode (imp (replace 5 70 oldTriple).encode (member 32 70)) :=
  certificate_correct old_triple_output70
end PASoundness.PAtoCompactMultiplicationCleanOldTripleOutput70
#print axioms PASoundness.PAtoCompactMultiplicationCleanOldTripleOutput70.old_triple_output70
#print axioms PASoundness.PAtoCompactMultiplicationCleanOldTripleOutput70.old_triple_output70_certificate
