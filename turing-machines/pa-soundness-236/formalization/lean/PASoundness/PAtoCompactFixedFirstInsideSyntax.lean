import PASoundness.PAtoCompactFixedFirstPreservedBase
import PASoundness.PAtoCompactMultiplicationRowCoverageAtEleven
import PASoundness.PAtoCompactMultiplicationOldGraphAtEleven
import PASoundness.PAtoCompactMultiplicationRowNoGarbageStep

/-! Syntactic alignments between the independently constructed row-step
clauses and the fixed-first preserved invariant. These identities do not
assert a K derivation, a row graph or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstInsideSyntax
open PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor

/-- The two modules use the same old-graph inclusion formula. -/
theorem preservation_agrees (h : Nat) :
    PAtoCompactFixedFirstPreservedBase.oldPreserved h =
      PAtoCompactMultiplicationOldGraphPreserve.oldPreserved h := by rfl

/-- The two modules use the same guarded row coverage formula. -/
theorem coverage_agrees (h : Nat) :
    PAtoCompactFixedFirstCoverageBase.coverage h =
      PAtoCompactMultiplicationRowCoveragePreserve.coverageAll h := by rfl

/-- The old no-garbage premise is literally the graph-7 invariant clause. -/
theorem old_no_garbage_agrees :
    PAtoCompactFixedFirstCoverageBase.noGarbage 7 =
      PAtoCompactMultiplicationRowOldEntry.oldNoGarbage := by rfl

/-- At the selected fresh names, the step's no-garbage conclusion is the
exact result of replacing the prefix name in the graph-11 invariant. -/
theorem new_no_garbage_agrees :
    replace 0 1 (PAtoCompactFixedFirstCoverageBase.noGarbage 11) =
      PAtoCompactMultiplicationRowNoGarbageStep.newNoGarbage := by decide

/-- The preservation conjunct is independent of the prefix name. -/
theorem preservation_prefix_vacuous :
    replace 0 1 (PAtoCompactFixedFirstPreservedBase.oldPreserved 11) =
      PAtoCompactFixedFirstPreservedBase.oldPreserved 11 := by decide

/-- The new invariant has exactly the three expected fixed-name clauses. -/
theorem new_invariant_shape :
    replace 0 1 (PAtoCompactFixedFirstPreservedBase.rowInvariantPreserved 11) =
      namedBoth (PAtoCompactFixedFirstPreservedBase.oldPreserved 11)
        (namedBoth (replace 0 1 (PAtoCompactFixedFirstCoverageBase.coverage 11))
          PAtoCompactMultiplicationRowNoGarbageStep.newNoGarbage) := by decide
end PASoundness.PAtoCompactFixedFirstInsideSyntax
#print axioms PASoundness.PAtoCompactFixedFirstInsideSyntax.preservation_agrees
#print axioms PASoundness.PAtoCompactFixedFirstInsideSyntax.coverage_agrees
#print axioms PASoundness.PAtoCompactFixedFirstInsideSyntax.old_no_garbage_agrees
#print axioms PASoundness.PAtoCompactFixedFirstInsideSyntax.new_no_garbage_agrees
#print axioms PASoundness.PAtoCompactFixedFirstInsideSyntax.preservation_prefix_vacuous
#print axioms PASoundness.PAtoCompactFixedFirstInsideSyntax.new_invariant_shape
