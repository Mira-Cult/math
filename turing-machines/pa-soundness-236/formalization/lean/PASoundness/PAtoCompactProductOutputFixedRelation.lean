import PASoundness.PAtoCompactProductOutputCanonical
import PASoundness.PAtoCompactProductMatchInputWitnesses
import PASoundness.PAtoCompactProductMatchCollectionConditional
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactSuccGraphOutputLift

/-! Eliminate the actual source product and output-equivalence graph witnesses
from the fixed-label canonical output constructor. The source candidate and
both supplied relations remain literal object-level antecedents. This is not
yet arbitrary-name or term-graph output transport. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputFixedRelation

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactProductMatchInputWitnesses PASoundness.PAtoCompactProductOutputReverseCoverage
open PASoundness.PAtoCompactProductOutputCollectionInsideConditional PASoundness.PAtoCompactProductOutputAssembledGraph
open PASoundness.PAtoCompactProductOutputCanonical PASoundness.PAtoCompactCandidateExact

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceProduct : Formula := replace 2 0 (replace 1 44 (replace 0 43
  PAtoCompactMultiplicationCandidate.productFormula))
def candidate : Formula := PAtoCompactProductMatchCollectionConditional.candidateFormula 0
def matrixGuard : Formula := namedBoth candidate relocatedMatrix
def baseGuard : Formula := namedBoth firstEquivalent candidate

theorem source_product_shape : sourceProduct = .ex 6 relocatedMatrix := by decide
theorem candidate_code : candidate.encode = candidateCode 0 81 77 78 72 64 73 59 75 := by rfl

def source_matrix_exists : KDerivation (imp sourceProduct.encode (existsCode 6 relocatedMatrix.encode)) := by
  rw [source_product_shape]
  exact CompactHilbertBasis.identity _

/-- For fixed graph witnesses6 and40, construct the canonical target
product using those exact source/product and output-isomorphism matrices. -/
noncomputable def matrix_point : KDerivation (imp matrixGuard.encode
    (imp firstMatrix.encode PAtoCompactProductOutputCanonical.targetProduct.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [firstMatrix.encode,matrixGuard.encode]
  have hf : Context Γ firstMatrix.encode := .head _ _
  have hm : Context Γ matrixGuard.encode := .hypothesis (by simp [Γ])
  have hm' : Context Γ (both candidate.encode relocatedMatrix.encode) := by
    simpa [matrixGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hm
  have hf' : Context Γ (both PAtoCompactProductMatchFactorImages.firstBijection.encode
      PAtoCompactProductMatchFactorOrderPoint.firstOrder.encode) := by
    simpa [firstMatrix, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hf
  have he : Context Γ extendedAssumptions.encode := by
    simpa [extendedAssumptions, assumptions, relocatedMatrix, namedBoth,
      CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro
        (Context.conjunctionIntro (Context.conjunctionRight hm') (Context.conjunctionLeft hf'))
        (Context.conjunctionRight hf')
  have hc : Context Γ (candidateCode 0 81 77 78 72 64 73 59 75) := by
    simpa [candidate_code] using Context.conjunctionLeft hm'
  exact .mp hc (.mp he (.closed canonical_product_output))

/-- Eliminate the output-equivalence graph40 while retaining the source
matrix and candidate. -/
noncomputable def matrix_from_equiv : KDerivation (imp baseGuard.encode
    (imp relocatedMatrix.encode PAtoCompactProductOutputCanonical.targetProduct.encode)) := by
  have h40 := guarded_exists_left 40 matrixGuard.encode firstMatrix.encode PAtoCompactProductOutputCanonical.targetProduct.encode
    (free_vacuity 40 matrixGuard (by decide)) (free_vacuity 40 PAtoCompactProductOutputCanonical.targetProduct (by decide)) matrix_point
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [relocatedMatrix.encode,baseGuard.encode]
  have hm : Context Γ relocatedMatrix.encode := .head _ _
  have hg : Context Γ baseGuard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both firstEquivalent.encode candidate.encode) := by
    simpa [baseGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  have hmg : Context Γ matrixGuard.encode := by
    simpa [matrixGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro (Context.conjunctionRight hg') hm
  have hw := Context.mp (Context.conjunctionLeft hg') (.closed first_matrix_exists)
  exact .mp hw (.mp hmg (.closed h40))

/-- Fixed labels: the supplied source product, output equivalence and source
candidate imply a target product with the same ordered factors. -/
noncomputable def fixed_relation_output : KDerivation (imp sourceProduct.encode
    (imp firstEquivalent.encode (imp candidate.encode PAtoCompactProductOutputCanonical.targetProduct.encode))) := by
  have h6 := guarded_exists_left 6 baseGuard.encode relocatedMatrix.encode PAtoCompactProductOutputCanonical.targetProduct.encode
    (free_vacuity 6 baseGuard (by decide)) (free_vacuity 6 PAtoCompactProductOutputCanonical.targetProduct (by decide)) matrix_from_equiv
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [candidate.encode,firstEquivalent.encode,sourceProduct.encode]
  have hc : Context Γ candidate.encode := .head _ _
  have he : Context Γ firstEquivalent.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ sourceProduct.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ baseGuard.encode := by
    simpa [baseGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro he hc
  have hw := Context.mp hs (.closed source_matrix_exists)
  exact .mp hw (.mp hg (.closed h6))

theorem fixed_relation_output_certificate : theoremCode (certificate fixed_relation_output) =
    imp sourceProduct.encode (imp firstEquivalent.encode (imp candidate.encode PAtoCompactProductOutputCanonical.targetProduct.encode)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputFixedRelation

#print axioms PASoundness.PAtoCompactProductOutputFixedRelation.matrix_point
#print axioms PASoundness.PAtoCompactProductOutputFixedRelation.matrix_from_equiv
#print axioms PASoundness.PAtoCompactProductOutputFixedRelation.fixed_relation_output
#print axioms PASoundness.PAtoCompactProductOutputFixedRelation.fixed_relation_output_certificate
