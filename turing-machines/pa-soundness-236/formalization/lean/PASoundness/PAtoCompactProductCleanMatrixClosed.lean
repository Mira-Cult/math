import PASoundness.PAtoCompactProductForwardClosed
import PASoundness.PAtoCompactProductCleanReverseClosed
import PASoundness.PAtoCompactProductCleanLexClosed

/-! Exact preservation of the literal multiplication matrix when the witness
graph is filtered to valid old nested triples. This is finite K derivation
data from a supplied matrix and filter; it asserts no graph existence,
product totality, or semantic soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductCleanMatrixClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductCleanFilter
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactProductForwardConditional PASoundness.PAtoCompactProductForwardClosed
open PASoundness.PAtoCompactProductCleanReverseClosed PASoundness.PAtoCompactProductCleanLexClosed
open PASoundness.PAtoCompactProductCleanLexTransfer
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Exact original and filtered named matrix shapes. -/
theorem original_matrix_shape : productMatrix =
    namedBoth forwardFormula (namedBoth reverseFormula lexFormula) := by rfl

theorem filtered_matrix_shape : replace 6 54 productMatrix =
    namedBoth (forwardAt 54) (namedBoth (replace 6 54 reverseFormula) filteredLex) := by decide

/-- The filtered graph preserves all three product-matrix clauses on the
same three old domain sets. No extra K proof-data inputs are required. -/
noncomputable def product_matrix_preserved : KDerivation (imp (filterCode 54)
    (imp productMatrix.encode (replace 6 54 productMatrix).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [productMatrix.encode,filterCode 54]
  have hm : Context Γ productMatrix.encode := .head _ _
  have hf : Context Γ (filterCode 54) := .hypothesis (by simp [Γ])
  have hshape : productMatrix.encode = both forwardFormula.encode
      (both reverseFormula.encode lexFormula.encode) := by rfl
  rw [hshape] at hm
  have hoF : Context Γ forwardFormula.encode := Context.conjunctionLeft hm
  have hoR : Context Γ reverseFormula.encode := Context.conjunctionLeft (Context.conjunctionRight hm)
  have hoL : Context Γ lexFormula.encode := Context.conjunctionRight (Context.conjunctionRight hm)
  have hnF : Context Γ (forwardAt 54).encode := .mp hoF (.mp hf (.closed forward_preserved))
  have hnR : Context Γ (replace 6 54 reverseFormula).encode := .mp hoR (.mp hf (.closed reverse_clause))
  have hnL : Context Γ filteredLex.encode := .mp hoL (.mp hf (.closed lex_preserved))
  have hc := Context.conjunctionIntro hnF (Context.conjunctionIntro hnR hnL)
  have htarget : (replace 6 54 productMatrix).encode =
      both (forwardAt 54).encode (both (replace 6 54 reverseFormula).encode filteredLex.encode) := by
    rw [filtered_matrix_shape]
    rfl
  rw [htarget]
  exact hc

theorem product_matrix_preserved_certificate : theoremCode (certificate product_matrix_preserved) =
    imp (filterCode 54) (imp productMatrix.encode (replace 6 54 productMatrix).encode) :=
  certificate_correct product_matrix_preserved
end PASoundness.PAtoCompactProductCleanMatrixClosed
#print axioms PASoundness.PAtoCompactProductCleanMatrixClosed.product_matrix_preserved
#print axioms PASoundness.PAtoCompactProductCleanMatrixClosed.product_matrix_preserved_certificate
