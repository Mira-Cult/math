import PASoundness.PAtoCompactEquivalentAliasGuardLift
import PASoundness.PAtoCompactPreparedAliasElimination

/-! The restricted endpoint target is K-equivalent to the canonical
quotient formula with fresh endpoint aliases bound by equality guards.
The guarded formula makes capture avoidance explicit. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactEquivalentEndpointAlias
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactEquivalentAliasInstantiation
open PASoundness.PAtoCompactEquivalentAliasGuardLift
open PASoundness.PAtoCompactPreparedAliasElimination
open PASoundness.PAtoCompactRestrictedEquivalentTarget
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The prepared guard in the two independently constructed modules agrees. -/
theorem prepared_guard_code : (guarded preparedAliases).encode = guardedPrepared.encode := rfl

/-- Actual K implication from the explicitly guarded canonical alias formula
to the restricted endpoint target. -/
def forward : KDerivation (imp (guarded originalAliases).encode endpointTarget.encode) := by
  have h : KDerivation (imp (guarded preparedAliases).encode endpointTarget.encode) :=
    prepared_alias_equiv.1
  exact compose PAtoCompactEquivalentAliasGuardLift.forward h

/-- The converse implication, with the same endpoint aliases and guards. -/
def backward : KDerivation (imp endpointTarget.encode (guarded originalAliases).encode) := by
  have h : KDerivation (imp endpointTarget.encode (guarded preparedAliases).encode) :=
    prepared_alias_equiv.2
  exact compose h PAtoCompactEquivalentAliasGuardLift.backward

theorem forward_certificate : theoremCode (certificate forward) =
    imp (guarded originalAliases).encode endpointTarget.encode := certificate_correct forward

theorem backward_certificate : theoremCode (certificate backward) =
    imp endpointTarget.encode (guarded originalAliases).encode := certificate_correct backward

end PASoundness.PAtoCompactEquivalentEndpointAlias

#print axioms PASoundness.PAtoCompactEquivalentEndpointAlias.forward
#print axioms PASoundness.PAtoCompactEquivalentEndpointAlias.backward
#print axioms PASoundness.PAtoCompactEquivalentEndpointAlias.forward_certificate
#print axioms PASoundness.PAtoCompactEquivalentEndpointAlias.backward_certificate
