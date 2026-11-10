import PASoundness.PAtoCompactRestrictedMatrixExists
import PASoundness.PAtoCompactRestrictionWitnessEight

/-! The endpoint-restricted matrix witness from supplied raw successor and
original isomorphism clauses. Canonical quotient alignment is separate. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedMatrixClosed
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactRestrictedMatrix
open PASoundness.PAtoCompactRestrictedMatrixExists PASoundness.PAtoCompactRestrictionWitnessEight
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- K constructs one graph satisfying both restricted bijection clauses and
the restricted order clause from the supplied two raw successors, target
transitivity and original bijection/order clauses. The endpoint filter is
constructed by selector 8 and the top edge follows from those hypotheses.
All names are syntactic; their object values may coincide. Code 1 is literal
`member 0 0`. The conclusion is the displayed matrix, not yet canonical E. -/
def restricted_matrix_closed : KDerivation
    (imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp (transitiveCode 5 11 12) (imp orderFormula.encode
        (imp bijectionFormula.encode (existsCode 8 restrictedMatrix)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [bijectionFormula.encode, orderFormula.encode, transitiveCode 5 11 12,
    successorCode 5 1 10, successorCode 2 0 9]
  have hb : Context Γ bijectionFormula.encode := .head _ _
  have ho : Context Γ orderFormula.encode := .hypothesis (by simp [Γ])
  have ht : Context Γ (transitiveCode 5 11 12) := .hypothesis (by simp [Γ])
  have hy : Context Γ (successorCode 5 1 10) := .hypothesis (by simp [Γ])
  have hx : Context Γ (successorCode 2 0 9) := .hypothesis (by simp [Γ])
  exact .mp (.closed restriction_exists_eight) (.mp hb (.mp ho (.mp ht
    (.mp hy (.mp hx (.closed restricted_matrix_exists))))))

theorem restricted_matrix_closed_certificate : theoremCode (certificate restricted_matrix_closed) =
    imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp (transitiveCode 5 11 12) (imp orderFormula.encode
        (imp bijectionFormula.encode (existsCode 8 restrictedMatrix))))) :=
  certificate_correct restricted_matrix_closed

end PASoundness.PAtoCompactRestrictedMatrixClosed

#print axioms PASoundness.PAtoCompactRestrictedMatrixClosed.restricted_matrix_closed
#print axioms PASoundness.PAtoCompactRestrictedMatrixClosed.restricted_matrix_closed_certificate
