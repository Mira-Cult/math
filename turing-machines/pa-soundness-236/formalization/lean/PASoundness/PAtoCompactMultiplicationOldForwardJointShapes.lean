import PASoundness.PAtoCompactProductCleanRebased303132
import PASoundness.PAtoCompactMultiplicationCleanOldMemberOutput
import PASoundness.PAtoCompactFixedFirstPreservedBase

/-! Capture-safe syntax alignment and finite K projections for combining
an old clean product witness with a full-prefix fixed-first row. These facts
do not construct the witnesses, prove graph functionality, or establish
multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationOldForwardJointShapes
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactFixedFirstPreservedBase

/-- The two constructions use exactly the same old-graph cleanliness formula. -/
theorem clean_eq : PASoundness.PAtoCompactMultiplicationCleanOldMemberOutput.oldClean =
    PASoundness.PAtoCompactProductCleanRebased303132.oldCleanActual := by decide

/-- Replacing the row-prefix label by the already free source label keeps the
old-inclusion, coverage, and no-garbage clauses in the displayed shape. -/
theorem row_shape : replace 0 31 (rowInvariantPreserved 64) = namedBoth (oldPreserved 64)
    (namedBoth (replace 0 31 (coverage 64)) (replace 0 31 (noGarbage 64))) := by decide

/-- The full-prefix row invariant implies both old-graph inclusion and its
own full-prefix no-garbage condition. -/
def row_projections : KDerivation (imp (replace 0 31 (rowInvariantPreserved 64)).encode
    (both (oldPreserved 64).encode (replace 0 31 (noGarbage 64)).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let T := (replace 0 31 (rowInvariantPreserved 64)).encode
  have h : Context [T] (both (oldPreserved 64).encode
      (both (replace 0 31 (coverage 64)).encode (replace 0 31 (noGarbage 64)).encode)) := by
    have h' : Context [T] T := .head [] T
    simpa [T,row_shape,namedBoth,Formula.not,Formula.encode,both,neg] using h'
  exact Context.conjunctionIntro (Context.conjunctionLeft h)
    (Context.conjunctionRight (Context.conjunctionRight h))

theorem row_projections_certificate : theoremCode (certificate row_projections) =
    imp (replace 0 31 (rowInvariantPreserved 64)).encode
      (both (oldPreserved 64).encode (replace 0 31 (noGarbage 64)).encode) :=
  certificate_correct row_projections
end PASoundness.PAtoCompactMultiplicationOldForwardJointShapes
#print axioms PASoundness.PAtoCompactMultiplicationOldForwardJointShapes.clean_eq
#print axioms PASoundness.PAtoCompactMultiplicationOldForwardJointShapes.row_shape
#print axioms PASoundness.PAtoCompactMultiplicationOldForwardJointShapes.row_projections
#print axioms PASoundness.PAtoCompactMultiplicationOldForwardJointShapes.row_projections_certificate
