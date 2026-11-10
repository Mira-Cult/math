import PASoundness.PAtoCompactGraphRestriction
import PASoundness.PAtoCompactSuccCongruenceData

/-! Fixed-name interfaces for transferring an isomorphism matrix to the
endpoint-filtered part of a supplied graph. This file defines syntax only;
it does not assert filter existence, matrix transfer or quotient laws. -/
namespace PASoundness.PAtoCompactCleanMatrixData
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactSuccCongruenceData

/-- Exact filter: original graph 10, restricted graph 6, endpoints 0/1,
test name 17. The represented filter graph is an explicit hypothesis. -/
def filterCode : Nat := filterGraph 10 6 17 (edgePredicate 17 0 1).encode

/-- Original isomorphism matrix, renamed from graph name 6 to name 10. -/
def oldMatrix10 : CompactNamed.Formula :=
  CompactNamed.replace 6 10 (namedBoth bijectionFormula orderFormula)

/-- The exact desired filtered-graph matrix, on the original 0/1 endpoints. -/
def filteredMatrix6 : CompactNamed.Formula := namedBoth bijectionFormula orderFormula

/-- Uniform edge equivalence on guarded endpoints. Fresh binders 28 and 29
avoid the internal graph/pair labels and the matrix's own test binders. -/
def guardedEdges : CompactNamed.Formula := .all 28 (.all 29
  (.imp (.member 0 28) (.imp (.member 1 29)
    (namedBoth (.imp (graphFormula 10 28 29) (graphFormula 6 28 29))
      (.imp (graphFormula 6 28 29) (graphFormula 10 28 29))))))

theorem filtered_matrix_code : filteredMatrix6.encode = oldMatrix := rfl

theorem old_matrix_free : oldMatrix10.free = {0,1,10} := by decide

theorem guarded_edges_free : guardedEdges.free = {0,1,6,10} := by decide

end PASoundness.PAtoCompactCleanMatrixData

#print axioms PASoundness.PAtoCompactCleanMatrixData.filtered_matrix_code
#print axioms PASoundness.PAtoCompactCleanMatrixData.old_matrix_free
#print axioms PASoundness.PAtoCompactCleanMatrixData.guarded_edges_free
