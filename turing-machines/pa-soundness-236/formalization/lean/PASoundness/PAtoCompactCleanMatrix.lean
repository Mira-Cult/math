import PASoundness.PAtoCompactCleanEdges
import PASoundness.PAtoCompactCleanRestriction
import PASoundness.PAtoCompactCleanBijection
import PASoundness.PAtoCompactCleanOrder

/-! Exact old-matrix and cleanliness transfer to a supplied endpoint filter.
The filter remains an antecedent; this module asserts no graph existence or
quotient theorem. -/
namespace PASoundness.PAtoCompactCleanMatrix
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.PAtoCompactCleanMatrixData PASoundness.PAtoCompactCleanEdges
open PASoundness.PAtoCompactCleanRestriction PASoundness.PAtoCompactCleanBijection
open PASoundness.PAtoCompactCleanOrder

/-- The supplied filter retains the old isomorphism matrix and is clean. -/
def clean_matrix : KDerivation (imp filterCode
    (imp oldMatrix10.encode (both oldMatrix cleanGraph))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldMatrix10.encode,filterCode]
  have ho : Context Γ oldMatrix10.encode := Context.head _ _
  have hf : Context Γ filterCode := .hypothesis (by simp [Γ])
  have he : Context Γ guardedEdges.encode := .mp hf (.closed guarded_edges)
  have hb : Context Γ bijectionFormula.encode := .mp ho (.mp he (.closed clean_bijection))
  have hr : Context Γ orderFormula.encode := .mp ho (.mp he (.closed clean_order_transfer))
  have hm : Context Γ oldMatrix := Context.conjunctionIntro hb hr
  have hc : Context Γ cleanGraph := .mp hf (.closed filter_is_clean)
  exact Context.conjunctionIntro hm hc

theorem clean_matrix_certificate : theoremCode (certificate clean_matrix) =
    imp filterCode (imp oldMatrix10.encode (both oldMatrix cleanGraph)) :=
  certificate_correct clean_matrix

end PASoundness.PAtoCompactCleanMatrix

#print axioms PASoundness.PAtoCompactCleanMatrix.clean_matrix
#print axioms PASoundness.PAtoCompactCleanMatrix.clean_matrix_certificate
