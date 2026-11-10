import PASoundness.PAtoCompactMultiplicationCandidate
import PASoundness.PAtoCompactZeroSuccessor

/-! Exact syntax of the product matrix at new factor names 38,31, result 45,
and graph 64. This is syntax only, not a graph existence or soundness proof. -/
namespace PASoundness.PAtoCompactProductNewMatrixShape
open PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def newMatrix : Formula := replace 6 64 (replace 2 45 (replace 1 31 (replace 0 38 productMatrix)))
def matrixForward : Formula := replace 6 64 (replace 2 45 (replace 1 31 (replace 0 38 forwardFormula)))
def matrixReverse : Formula := replace 6 64 (replace 2 45 (replace 1 31 (replace 0 38 reverseFormula)))
def matrixLex : Formula := replace 2 45 (replace 1 31 (replace 0 38 (replace 6 64 lexFormula)))

/-- The original matrix's exact three clauses remain attached to the same
named graph 64. All substitutions act on named syntax only. -/
theorem matrix_clause_shape : newMatrix =
    namedBoth matrixForward (namedBoth matrixReverse matrixLex) := by decide

end PASoundness.PAtoCompactProductNewMatrixShape
#print axioms PASoundness.PAtoCompactProductNewMatrixShape.matrix_clause_shape
