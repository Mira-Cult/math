import PASoundness.PAtoCompactProductCleanLexTransfer

/-! Pointwise lexicographic comparison from an explicitly supplied old product
matrix. Both triples and all six endpoint-membership guards remain in the
antecedent. This does not infer any order about a transported output cut, any
new graph edge, multiplication totality, or PA soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOldLexPoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductCleanLexTransfer
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The old product matrix with its represented graph at name 10. -/
def oldMatrixAtTen : Formula := replace 6 10 productMatrix

/-- The actual product matrix proves its literal point clause. The point
antecedent includes all six endpoint memberships and both old triples, and
the consequent contains both directions of the lexicographic comparison. -/
def matrix_point : KDerivation (imp productMatrix.encode (point 6).encode) := by
  have h3 := allSpecialize 3 (.all 4 (.all 5 (.all 7 (.all 8 (.all 9 (point 6)))))) (by decide)
  have h4 := allSpecialize 4 (.all 5 (.all 7 (.all 8 (.all 9 (point 6))))) (by decide)
  have h5 := allSpecialize 5 (.all 7 (.all 8 (.all 9 (point 6)))) (by decide)
  have h7 := allSpecialize 7 (.all 8 (.all 9 (point 6))) (by decide)
  have h8 := allSpecialize 8 (.all 9 (point 6)) (by decide)
  have h9 := allSpecialize 9 (point 6) (by decide)
  have hp : KDerivation (imp lexFormula.encode (point 6).encode) := by
    rw [original_shape]
    exact compose h3 (compose h4 (compose h5 (compose h7 (compose h8 h9))))
  apply Context.closeEmpty
  apply Context.deduction
  have hm : Context [productMatrix.encode] productMatrix.encode := .head _ _
  change Context [productMatrix.encode] (both forwardFormula.encode
    (both reverseFormula.encode lexFormula.encode)) at hm
  exact .mp (Context.conjunctionRight (Context.conjunctionRight hm)) (.closed hp)

/-- Capture-safe relocation of the same comparison to the graph name used by
the row-augmentation construction. No equality of graph representatives is
assumed; both the matrix and triples are instantiated at graph 10. -/
def matrix_point_at_ten : KDerivation (imp oldMatrixAtTen.encode (point 10).encode) := by
  let f : Formula := .imp productMatrix (point 6)
  have hi := universalInstance 6 10 f (by decide) (by decide) (by decide)
  have hf : replace 6 10 f = .imp oldMatrixAtTen (point 10) := by decide
  rw [hf] at hi
  have h : KDerivation f.encode := matrix_point
  exact .mp (.generalize 6 h) hi

theorem matrix_point_certificate : theoremCode (certificate matrix_point) =
    imp productMatrix.encode (point 6).encode := certificate_correct matrix_point

theorem matrix_point_at_ten_certificate : theoremCode (certificate matrix_point_at_ten) =
    imp oldMatrixAtTen.encode (point 10).encode := certificate_correct matrix_point_at_ten
end PASoundness.PAtoCompactProductOldLexPoint
#print axioms PASoundness.PAtoCompactProductOldLexPoint.matrix_point
#print axioms PASoundness.PAtoCompactProductOldLexPoint.matrix_point_at_ten
#print axioms PASoundness.PAtoCompactProductOldLexPoint.matrix_point_certificate
#print axioms PASoundness.PAtoCompactProductOldLexPoint.matrix_point_at_ten_certificate
