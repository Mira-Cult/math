import PASoundness.PAtoCompactIsoConditionalWrapper
import PASoundness.PAtoCompactInverseAlpha
import PASoundness.PAtoCompactRestrictedInverseClause

/-! One exact reversed-matrix clause under restricted inverse correspondence.
The candidate itself is unchanged. Remaining clauses, actual graph existence,
and the complete quotient or arithmetic interpretation are not established. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedInverseFirst
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactIsoConditionalWrapper PASoundness.PAtoCompactInverseAlpha
open PASoundness.PAtoCompactRestrictedInverseClause
open PASoundness.PAtoCompactRestrictedInverseExists
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

def restrictedInverseMatrix : Formula := conj (.all 3 forwardFormula) (.all 3 backwardFormula)

def matrixFirst : Formula := match reverseMatrix7 with
  | .imp (.imp (.imp (.imp first _) .bottom) _) .bottom => first
  | _ => .truth

theorem first_matches_matrix : swappedFirst = matrixFirst := by decide

theorem image_clause_syntax : newImageClause = reverseImageFormula.encode := rfl

/-- The exact first reversed-bijection clause follows from the forward matrix
and correspondence constrained to pairs from its two domains. -/
def guarded_matrix_first_clause : KDerivation
    (imp forwardMatrix.encode (imp restrictedInverseMatrix.encode matrixFirst.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [restrictedInverseMatrix.encode,forwardMatrix.encode]
  have hm : Context Γ forwardMatrix.encode := .hypothesis (by simp [Γ])
  have hi : Context Γ restrictedInverseMatrix.encode := Context.head _ _
  have hb : Context Γ PASoundness.PAtoCompactOrderIsomorphism.bijectionFormula.encode :=
    Context.conjunctionLeft hm
  have hp : Context Γ oldPreimageClause := Context.conjunctionRight hb
  have hf : Context Γ globalForward := Context.conjunctionLeft hi
  have hr : Context Γ globalBackward := Context.conjunctionRight hi
  have ho : Context Γ newImageClause :=
    .mp hp (.mp hr (.mp hf (.closed guarded_preimage_clause)))
  have ha : KDerivation (imp newImageClause swappedFirst.encode) := by
    rw [image_clause_syntax]
    exact reverse_image_to_swapped_first
  rw [← first_matches_matrix]
  exact .mp ho (.closed ha)

theorem guarded_matrix_first_clause_certificate :
    theoremCode (certificate guarded_matrix_first_clause) =
      imp forwardMatrix.encode (imp restrictedInverseMatrix.encode matrixFirst.encode) :=
  certificate_correct guarded_matrix_first_clause

end PASoundness.PAtoCompactRestrictedInverseFirst

#print axioms PASoundness.PAtoCompactRestrictedInverseFirst.guarded_matrix_first_clause
#print axioms PASoundness.PAtoCompactRestrictedInverseFirst.guarded_matrix_first_clause_certificate
