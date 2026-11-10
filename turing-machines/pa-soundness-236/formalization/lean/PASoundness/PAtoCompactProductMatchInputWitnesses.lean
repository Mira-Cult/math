import PASoundness.PAtoCompactProductMatchEquivFixed
import PASoundness.PAtoCompactProductMatchFactorOrderPoint

/-! Expose the exact graph matrices needed by the fixed-label product
congruence from supplied product and factor-equivalence formulas. All graph
names are syntactic labels; no represented values are assumed distinct. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchInputWitnesses

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductMatchTargetOutput
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductMatchFactorOrderPoint

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def targetProduct : Formula := replace 2 44 (replace 1 43 (replace 0 42 productFormula))
def targetBefore : Formula := replace 2 44 (replace 1 43 (replace 0 42 productMatrix))
def firstEquivalent : Formula := replace 1 42 equivalentFormula
def firstBefore : Formula := replace 1 42 (namedBoth bijectionFormula orderFormula)
def firstMatrix : Formula := namedBoth firstBijection firstOrder
def secondEquivalent : Formula := replace 0 1 (replace 1 43 equivalentFormula)
def secondBefore : Formula := replace 0 1 (replace 1 43 (namedBoth bijectionFormula orderFormula))
def secondMatrix : Formula := namedBoth secondBijection secondOrder

theorem target_product_shape : targetProduct = .ex 6 targetBefore := by decide
theorem target_matrix_shape : replace 6 45 targetBefore = targetMatrix := by decide
theorem first_equivalent_shape : firstEquivalent = .ex 6 firstBefore := by decide
theorem first_matrix_shape : replace 6 40 firstBefore = firstMatrix := by decide
theorem second_equivalent_shape : secondEquivalent = .ex 6 secondBefore := by decide
theorem second_matrix_shape : replace 6 41 secondBefore = secondMatrix := by decide

def target_matrix_exists : KDerivation (imp targetProduct.encode (existsCode 45 targetMatrix.encode)) := by
  have h := (existentialAlpha 6 45 targetBefore (by decide) (by decide) (by decide)).1
  rw [target_matrix_shape] at h
  simpa [target_product_shape, Formula.encode] using h

def first_matrix_exists : KDerivation (imp firstEquivalent.encode (existsCode 40 firstMatrix.encode)) := by
  have h := (existentialAlpha 6 40 firstBefore (by decide) (by decide) (by decide)).1
  rw [first_matrix_shape] at h
  simpa [first_equivalent_shape, Formula.encode] using h

def second_matrix_exists : KDerivation (imp secondEquivalent.encode (existsCode 41 secondMatrix.encode)) := by
  have h := (existentialAlpha 6 41 secondBefore (by decide) (by decide) (by decide)).1
  rw [second_matrix_shape] at h
  simpa [second_equivalent_shape, Formula.encode] using h

theorem target_matrix_exists_certificate : theoremCode (certificate target_matrix_exists) =
    imp targetProduct.encode (existsCode 45 targetMatrix.encode) := certificate_correct _
theorem first_matrix_exists_certificate : theoremCode (certificate first_matrix_exists) =
    imp firstEquivalent.encode (existsCode 40 firstMatrix.encode) := certificate_correct _
theorem second_matrix_exists_certificate : theoremCode (certificate second_matrix_exists) =
    imp secondEquivalent.encode (existsCode 41 secondMatrix.encode) := certificate_correct _

end PASoundness.PAtoCompactProductMatchInputWitnesses

#print axioms PASoundness.PAtoCompactProductMatchInputWitnesses.target_matrix_exists
#print axioms PASoundness.PAtoCompactProductMatchInputWitnesses.first_matrix_exists
#print axioms PASoundness.PAtoCompactProductMatchInputWitnesses.second_matrix_exists
#print axioms PASoundness.PAtoCompactProductMatchInputWitnesses.target_matrix_exists_certificate
#print axioms PASoundness.PAtoCompactProductMatchInputWitnesses.first_matrix_exists_certificate
#print axioms PASoundness.PAtoCompactProductMatchInputWitnesses.second_matrix_exists_certificate
