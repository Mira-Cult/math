import PASoundness.PAtoCompactRestrictedInverseFirst
import PASoundness.PAtoCompactRestrictedInverseSecondRebind
import PASoundness.PAtoCompactRestrictedInverseSecondExists
import PASoundness.PAtoCompactReversePreimageAlpha

/-! The second exact reversed-bijection clause follows under correspondence
restricted to the two displayed domains. The original candidate is unchanged;
this constructs neither an inverse graph nor full quotient symmetry. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedInverseSecond
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactIsoConditionalWrapper
open PASoundness.PAtoCompactRestrictedInverseFirst PASoundness.PAtoCompactReversePreimageAlpha
open PASoundness.PAtoCompactRestrictedInverseSecondRebind
open PASoundness.PAtoCompactRestrictedInverseSecondExists
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Exact second bijection clause extracted from the swapped matrix. -/
def matrixSecond : Formula := match reverseMatrix7 with
  | .imp (.imp (.imp (.imp _ (.imp second .bottom)) .bottom) _) .bottom => second
  | _ => .truth

theorem second_matches_matrix : swappedSecond = matrixSecond := by decide

theorem preimage_clause_syntax : newPreimageClause = reversePreimageFormula.encode := rfl

/-- The exact second reversed-bijection clause follows from the forward matrix
and inverse correspondence constrained to the two domains. -/
def guarded_matrix_second_clause : KDerivation
    (imp forwardMatrix.encode (imp restrictedInverseMatrix.encode matrixSecond.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [restrictedInverseMatrix.encode,forwardMatrix.encode]
  have hm : Context Γ forwardMatrix.encode := .hypothesis (by simp [Γ])
  have hi : Context Γ restrictedInverseMatrix.encode := Context.head _ _
  have hb : Context Γ bijectionFormula.encode := Context.conjunctionLeft hm
  have hp : Context Γ oldImageClause := Context.conjunctionLeft hb
  have hf : Context Γ PASoundness.PAtoCompactRestrictedInverseClause.globalForward :=
    Context.conjunctionLeft hi
  have hr : Context Γ PASoundness.PAtoCompactRestrictedInverseClause.globalBackward :=
    Context.conjunctionRight hi
  have hF : Context Γ globalForward := by
    exact .mp hf (.closed rebind_forward)
  have hR : Context Γ globalBackward := by
    exact .mp hr (.closed rebind_reverse)
  have ho : Context Γ newPreimageClause :=
    .mp hp (.mp hR (.mp hF (.closed guarded_image_clause)))
  have ha : KDerivation (imp newPreimageClause swappedSecond.encode) := by
    rw [preimage_clause_syntax]
    exact reverse_preimage_to_swapped_second
  rw [← second_matches_matrix]
  exact .mp ho (.closed ha)

theorem guarded_matrix_second_clause_certificate :
    theoremCode (certificate guarded_matrix_second_clause) =
      imp forwardMatrix.encode (imp restrictedInverseMatrix.encode matrixSecond.encode) :=
  certificate_correct guarded_matrix_second_clause

end PASoundness.PAtoCompactRestrictedInverseSecond

#print axioms PASoundness.PAtoCompactRestrictedInverseSecond.guarded_matrix_second_clause
#print axioms PASoundness.PAtoCompactRestrictedInverseSecond.guarded_matrix_second_clause_certificate
