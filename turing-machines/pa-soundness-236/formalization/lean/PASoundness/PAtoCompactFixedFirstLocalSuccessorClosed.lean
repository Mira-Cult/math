import PASoundness.PAtoCompactFixedFirstGuardedOldExists
import PASoundness.PAtoCompactFixedFirstBranchJoin

/-! A closed finite K successor step for the fixed-first row-graph predicate.
The supplied map bijection remains an object-level hypothesis. This is the
local induction step, not yet quantified candidate induction, row collection,
or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstLocalSuccessorClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFixedFirstPreservedBase
open PASoundness.PAtoCompactMultiplicationRowMapEdge PASoundness.PAtoCompactFixedFirstBranchJoin
open PASoundness.PAtoCompactFixedFirstGuardedOldExists

/-- A graph preserving the old graph, covering the current row prefix, and
having no entries beyond the old graph or represented row entries. -/
def rowPredicate : Formula := .ex 7 (rowInvariantPreserved 7)

/-- The graph-witness binder remains unchanged when the prefix is replaced. -/
theorem successor_predicate_shape : replace 0 1 rowPredicate =
    .ex 7 (replace 0 1 (rowInvariantPreserved 7)) := by decide

/-- Exact named syntax inventory for subsequent capture-safe induction. -/
theorem predicate_names : rowPredicate.names = {0,3,4,5,6,7,9,10,19,20,21,22,30,31} := by decide

theorem predicate_binders : rowPredicate.binders = {3,4,5,7,9,19,20,21,22} := by decide

theorem predicate_free : rowPredicate.free = {0,6,10,30,31} := by decide

/-- From a supplied F bijection and a prefix successor, every existential row
witness extends to a successor-prefix witness. The inside and outside branches
are both actual finite K derivations; no pair-representative uniqueness is used. -/
def local_successor : KDerivation (imp mapBijection.encode
    (imp (successorCode 0 1 2)
      (imp rowPredicate.encode (replace 0 1 rowPredicate).encode))) := by
  rw [successor_predicate_shape]
  exact join inside_from_old_exists

theorem local_successor_certificate : theoremCode (certificate local_successor) =
    imp mapBijection.encode (imp (successorCode 0 1 2)
      (imp rowPredicate.encode (replace 0 1 rowPredicate).encode)) := certificate_correct _
end PASoundness.PAtoCompactFixedFirstLocalSuccessorClosed
#print axioms PASoundness.PAtoCompactFixedFirstLocalSuccessorClosed.successor_predicate_shape
#print axioms PASoundness.PAtoCompactFixedFirstLocalSuccessorClosed.predicate_names
#print axioms PASoundness.PAtoCompactFixedFirstLocalSuccessorClosed.predicate_binders
#print axioms PASoundness.PAtoCompactFixedFirstLocalSuccessorClosed.predicate_free
#print axioms PASoundness.PAtoCompactFixedFirstLocalSuccessorClosed.local_successor
#print axioms PASoundness.PAtoCompactFixedFirstLocalSuccessorClosed.local_successor_certificate
