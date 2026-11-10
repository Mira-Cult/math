import PASoundness.PAtoCompactSuffixGraphMatrix
import PASoundness.PAtoCompactSuffixGraphQuotientAlignment
import PASoundness.PAtoCompactSuffixOrderAlpha

/-! Exact syntax alignment between the suffix graph matrix and the previously
alpha-prepared quotient isomorphism. This does not construct graph8 or prove
that either suffix filter exists. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuffixGraphMatrixAlignment
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuffixGraphForwardCoverage PASoundness.PAtoCompactSuffixGraphReverseCoverage
open PASoundness.PAtoCompactSuffixGraphMatrix PASoundness.PAtoCompactSuffixGraphQuotientAlignment
open PASoundness.PAtoCompactSuffixOrderAlpha
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def namedForward : Formula := .all 7
  (.imp (.member 40 7) (.ex 3 suffixForwardWitness))
private def namedReverse : Formula := .all 3
  (.imp (.member 41 3) (.ex 7 suffixReverseWitness))
def suffixMatrixNamed : Formula := namedBoth (namedBoth namedForward namedReverse) suffixAlphaOrder

/-- All bound variables were changed in the imported preparation before the
free endpoint names were set to 40 and 41. This is a syntax identity only. -/
theorem suffix_prepared_shape : suffixPrepared = .ex 8 suffixMatrixNamed := by decide

/-- The exact named matrix has the same code as the three independently
derived clauses for the same graph and endpoints. -/
theorem suffix_matrix_body_code : suffixMatrixNamed.encode = suffixMatrix := by
  simp only [suffixMatrixNamed, namedForward, namedReverse, suffixMatrix, suffixForward,
    suffixReverse, suffix_alpha_order_code, namedBoth, Formula.not, Formula.encode,
    CompactProof.both, CompactProof.neg]

/-- The prepared isomorphism binds graph8 over that exact matrix. -/
theorem suffix_prepared_code : suffixPrepared.encode = existsCode 8 suffixMatrix := by
  rw [suffix_prepared_shape]
  simp only [Formula.encode, suffix_matrix_body_code]

/-- K proof data carrying a graph8 witness for the assembled suffix matrix to
the literal named isomorphism between the two supplied suffix sets. -/
noncomputable def suffix_matrix_to_equivalent : KDerivation
    (imp (existsCode 8 suffixMatrix) suffixEquivalent.encode) := by
  rw [← suffix_prepared_code]
  exact suffix_prepared_to_equivalent

theorem suffix_matrix_to_equivalent_certificate :
    theoremCode (certificate suffix_matrix_to_equivalent) =
      imp (existsCode 8 suffixMatrix) suffixEquivalent.encode :=
  certificate_correct suffix_matrix_to_equivalent

end PASoundness.PAtoCompactSuffixGraphMatrixAlignment

#print axioms PASoundness.PAtoCompactSuffixGraphMatrixAlignment.suffix_prepared_shape
#print axioms PASoundness.PAtoCompactSuffixGraphMatrixAlignment.suffixMatrixNamed
#print axioms PASoundness.PAtoCompactSuffixGraphMatrixAlignment.suffix_matrix_body_code
#print axioms PASoundness.PAtoCompactSuffixGraphMatrixAlignment.suffix_prepared_code
#print axioms PASoundness.PAtoCompactSuffixGraphMatrixAlignment.suffix_matrix_to_equivalent
#print axioms PASoundness.PAtoCompactSuffixGraphMatrixAlignment.suffix_matrix_to_equivalent_certificate
