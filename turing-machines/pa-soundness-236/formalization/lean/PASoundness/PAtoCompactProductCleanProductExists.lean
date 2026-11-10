import PASoundness.PAtoCompactProductCleanMatrixClosed
import PASoundness.PAtoCompactProductCleanFilterFixed
import PASoundness.PAtoCompactProductCleanMembers

/-! A product witness can be replaced inside K by a graph that contains only
valid old nested triples, while preserving the actual literal product matrix.
This is a graph-cleaning theorem, not multiplication totality or a graph-row
collection theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductCleanProductExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactProductCleanFilter PASoundness.PAtoCompactProductCleanFilterFixed
open PASoundness.PAtoCompactProductCleanMembers PASoundness.PAtoCompactProductCleanMatrixClosed
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The product matrix at the fresh, filtered graph label. -/
def filteredMatrix : Formula := replace 6 54 productMatrix
/-- The same graph witness is required to satisfy the matrix and cleanliness. -/
def cleanWitness : Formula := .ex 54 (namedBoth filteredMatrix
  (.all 19 (.imp (.member 54 19) (cleanPredicate 19))))
private theorem cleanWitness_code : cleanWitness.encode =
    existsCode 54 (both filteredMatrix.encode cleanCode) := by rfl

private noncomputable def matrix_with_filter : KDerivation (imp productMatrix.encode
    (imp (filterCode 54) (both filteredMatrix.encode cleanCode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [filterCode 54,productMatrix.encode]
  have hf : Context Γ (filterCode 54) := .head _ _
  have hm : Context Γ productMatrix.encode := .hypothesis (by simp [Γ])
  have hnew : Context Γ filteredMatrix.encode :=
    .mp hm (.mp hf (.closed product_matrix_preserved))
  have hc : Context Γ cleanCode := .mp hf (.closed filter_is_clean)
  exact Context.conjunctionIntro hnew hc

/-- A supplied product matrix entails existence of a clean filtered graph
with the exact same three product domains. -/
noncomputable def clean_of_matrix : KDerivation (imp productMatrix.encode cleanWitness.encode) := by
  have hv : KDerivation (imp productMatrix.encode (allCode 54 productMatrix.encode)) :=
    productMatrix.vacuity 54 (by decide)
  have hc := conditionalExistsCongr 54 hv matrix_with_filter
  apply Context.closeEmpty
  apply Context.deduction
  have hm : Context [productMatrix.encode] productMatrix.encode := .head _ _
  have hex : Context [productMatrix.encode] (existsCode 54 (filterCode 54)) := .closed product_filter_exists_fixed
  have hnew := Context.mp hex (Context.mp hm (.closed hc))
  simpa only [cleanWitness_code] using hnew

/-- From the original literal product relation, K constructs a clean graph
that still satisfies all three clauses of the product matrix. -/
noncomputable def clean_product_exists : KDerivation (imp productFormula.encode cleanWitness.encode) := by
  have hv : KDerivation (imp cleanWitness.encode (allCode 6 cleanWitness.encode)) :=
    cleanWitness.vacuity 6 (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  have h := Context.head [] productFormula.encode
  change Context [productFormula.encode] (existsCode 6 productMatrix.encode) at h
  exact Context.existsElim hv (.closed (.generalize 6 clean_of_matrix)) h

theorem clean_product_exists_certificate : theoremCode (certificate clean_product_exists) =
    imp productFormula.encode cleanWitness.encode := certificate_correct clean_product_exists
end PASoundness.PAtoCompactProductCleanProductExists
#print axioms PASoundness.PAtoCompactProductCleanProductExists.clean_of_matrix
#print axioms PASoundness.PAtoCompactProductCleanProductExists.clean_product_exists
#print axioms PASoundness.PAtoCompactProductCleanProductExists.clean_product_exists_certificate
