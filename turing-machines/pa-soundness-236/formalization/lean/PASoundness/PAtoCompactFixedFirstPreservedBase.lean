import PASoundness.PAtoCompactFixedFirstCoverageBase

/-! The empty-prefix fixed-first row base with explicit preservation of the
old graph. This strengthens the coverage/no-garbage invariant by requiring
all old graph entries to remain in the new graph. No nonempty row collection,
multiplication totality or PA interpretation is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstPreservedBase
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactFixedFirstCoverageBase
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Every old graph entry remains present in the new graph. -/
def oldPreserved (h : Nat) : Formula := .all 9 (.imp (.member 10 9) (.member h 9))

/-- Preservation together with existential row coverage and no garbage. -/
def rowInvariantPreserved (h : Nat) : Formula :=
  namedBoth (oldPreserved h) (rowInvariant h)

/-- The old graph preserves itself, independently of every other parameter. -/
def old_preserved_self : KDerivation (oldPreserved 10).encode := by
  change KDerivation (allCode 9 (imp (member 10 9) (member 10 9)))
  exact .generalize 9 (CompactHilbertBasis.identity (member 10 9))

/-- If the prefix is zero, the old graph itself satisfies the strengthened
invariant; no existence or uniqueness hypothesis for the source graph occurs. -/
def zero_preserved_invariant : KDerivation
    (imp (zeroCode 0 12) (rowInvariantPreserved 10).encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [zeroCode 0 12]
  have hz : Context Γ (zeroCode 0 12) := .head _ _
  have hw : Context Γ (rowInvariant 10).encode := .mp hz (.closed zero_row_invariant)
  have hp : Context Γ (oldPreserved 10).encode := .closed old_preserved_self
  have h := Context.conjunctionIntro hp hw
  simpa [rowInvariantPreserved,namedBoth,Formula.not,Formula.encode,both,neg] using h

/-- K supplies a row graph satisfying preservation, coverage and no garbage
at zero prefix; the witness is the arbitrary old graph 10. -/
def zero_preserved_exists : KDerivation
    (imp (zeroCode 0 12) (existsCode 7 (rowInvariantPreserved 7).encode)) := by
  have hi := exists_variable_intro 7 10 (rowInvariantPreserved 7)
    (by decide) (by decide) (by decide)
  have hr : CompactNamed.replace 7 10 (rowInvariantPreserved 7) = rowInvariantPreserved 10 := by decide
  rw [hr] at hi
  exact compose zero_preserved_invariant hi

theorem zero_preserved_exists_certificate : theoremCode (certificate zero_preserved_exists) =
    imp (zeroCode 0 12) (existsCode 7 (rowInvariantPreserved 7).encode) :=
  certificate_correct zero_preserved_exists
end PASoundness.PAtoCompactFixedFirstPreservedBase
#print axioms PASoundness.PAtoCompactFixedFirstPreservedBase.old_preserved_self
#print axioms PASoundness.PAtoCompactFixedFirstPreservedBase.zero_preserved_invariant
#print axioms PASoundness.PAtoCompactFixedFirstPreservedBase.zero_preserved_exists
#print axioms PASoundness.PAtoCompactFixedFirstPreservedBase.zero_preserved_exists_certificate
