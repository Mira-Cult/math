import PASoundness.PAtoCompactMultiplicationRowPrefixTransport
import PASoundness.CompactQuantifiers

/-! The old-entry branch of the proposed multiplication-row no-garbage
invariant, under literal prefix inclusion. The same represented row-entry
witness is preserved; no assertion about a new graph entry, collection,
product existence, or representative uniqueness is made. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationRowOldEntry
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationRowPrefixTransport
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Original graph 10 or the exact represented row witness for prefix k. -/
def entry (k : Nat) : Formula := namedEither (.member 10 9) (rowWitness k)

/-- The old graph has no entries beyond original graph entries or represented
row witnesses for prefix 0. Label 9 is the bound entry name. -/
def oldNoGarbage : Formula := .all 9 (.imp (.member 7 9) (entry 0))

/-- An old graph entry satisfies the no-garbage alternative for the new
prefix, under the old no-garbage invariant and prefix inclusion. -/
def old_entry_preserved : KDerivation (imp prefixInclusion
    (imp oldNoGarbage.encode (imp (member 7 9) (entry 1).encode))) := by
  let f : Formula := .imp (.member 7 9) (entry 0)
  have hs := allSpecialize 9 f (by decide)
  have hs' : KDerivation (imp oldNoGarbage.encode
      (imp (member 7 9) (either (member 10 9) (rowWitness 0).encode))) := by
    simpa [oldNoGarbage,f,entry,namedEither,Formula.not,Formula.encode,neg,either] using hs
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 7 9, oldNoGarbage.encode, prefixInclusion]
  have hm : Context Γ (member 7 9) := .head _ _
  have hn : Context Γ oldNoGarbage.encode := .hypothesis (by simp [Γ])
  have hi : Context Γ prefixInclusion := .hypothesis (by simp [Γ])
  have hc : Context Γ (either (member 10 9) (rowWitness 0).encode) :=
    .mp hm (.mp hn (.closed hs'))
  change Context Γ (either (member 10 9) (rowWitness 1).encode)
  apply Context.disjunctionElim hc
  · exact Context.disjunctionLeft (.head _ _)
  · have hr : Context ((rowWitness 0).encode :: Γ) (rowWitness 0).encode := .head _ _
    have hp : Context ((rowWitness 0).encode :: Γ) prefixInclusion := .under hi _
    exact Context.disjunctionRight (.mp hr (.mp hp (.closed row_witness_prefix_inclusion)))

theorem old_entry_preserved_certificate : theoremCode (certificate old_entry_preserved) =
    imp prefixInclusion (imp oldNoGarbage.encode (imp (member 7 9) (entry 1).encode)) :=
  certificate_correct old_entry_preserved
end PASoundness.PAtoCompactMultiplicationRowOldEntry
#print axioms PASoundness.PAtoCompactMultiplicationRowOldEntry.old_entry_preserved
#print axioms PASoundness.PAtoCompactMultiplicationRowOldEntry.old_entry_preserved_certificate
