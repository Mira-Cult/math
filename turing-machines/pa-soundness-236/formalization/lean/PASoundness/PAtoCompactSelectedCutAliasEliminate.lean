import PASoundness.PAtoCompactPreparedAliasElimination
import PASoundness.PAtoCompactEquivalentAliasInstantiation
import PASoundness.PAtoCompactStagedEquivalenceAligned

/-! Eliminate fresh endpoint aliases for an explicitly guarded cut
isomorphism. This does not construct the guard or rename a graph witness. -/
namespace PASoundness.PAtoCompactSelectedCutAliasEliminate
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactPreparedAliasElimination PASoundness.PAtoCompactEquivalentAliasInstantiation
open PASoundness.PAtoCompactStagedEquivalenceAlpha PASoundness.PAtoCompactStagedEquivalenceAligned
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The original equality formula with its free alias names changed from
40,41 to 70,71. These are syntactic names, not distinct object assumptions. -/
def freshAliases : Formula := replace 41 71 (replace 40 70 originalAliases)

/-- Fresh aliases are explicitly tied to the intended cut labels 33,41.
In particular the target endpoint 41 is not shadowed by its alias binder. -/
def freshGuard : Formula := .ex 70 (namedBoth (.equal 70 33)
  (.ex 71 (namedBoth (.equal 71 41) freshAliases)))

private def mid : Formula := replace 71 41 freshAliases
private theorem final_shape : replace 70 33 mid = rawStaged 33 41 := by decide

/-- The equality guards may be removed using finite K equality substitution;
the resulting staged raw equivalence is then aligned to the allocator-100
relation. Neither a graph nor the guarded hypothesis is constructed here. -/
def fresh_guard_to_allocated : KDerivation
    (imp freshGuard.encode (equivAt 100 33 41).encode) := by
  have hi := alias_equiv 71 41 72 freshAliases (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have ho := alias_equiv 70 33 73 mid (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hlift := existsCongr 70
    (contrapose (implicationCongr (CompactHilbertBasis.identity (equal 70 33)) (contrapose hi.1)))
  have hf : KDerivation (imp freshGuard.encode (aliasFormula 70 33 mid).encode) := by
    exact hlift
  rw [final_shape] at ho
  exact compose hf (compose ho.1
    (staged_to_allocated 33 41 (by decide) (by decide) (by decide) (by decide) (by decide)))

theorem fresh_guard_to_allocated_certificate : theoremCode (certificate fresh_guard_to_allocated) =
    imp freshGuard.encode (equivAt 100 33 41).encode := certificate_correct fresh_guard_to_allocated
end PASoundness.PAtoCompactSelectedCutAliasEliminate

#print axioms PASoundness.PAtoCompactSelectedCutAliasEliminate.freshAliases
#print axioms PASoundness.PAtoCompactSelectedCutAliasEliminate.freshGuard
#print axioms PASoundness.PAtoCompactSelectedCutAliasEliminate.fresh_guard_to_allocated
#print axioms PASoundness.PAtoCompactSelectedCutAliasEliminate.fresh_guard_to_allocated_certificate
