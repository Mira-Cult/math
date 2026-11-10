import PASoundness.PAtoCompactRestrictedInverseFirst
import PASoundness.PAtoCompactIsoTransportWrapper
import PASoundness.PAtoCompactOrderIsoSwap
import PASoundness.PAtoCompactOrderIsoRestrictedAll
import PASoundness.PAtoCompactOrderIsoReverseAlpha
import PASoundness.PAtoCompactRestrictedInverseSecond

/-! Conditional symmetry for the unchanged concrete order-isomorphism
candidate, using inverse-edge correspondence only for pairs in the two
input domains. The represented inverse graph remains an explicit premise. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedSymmetry
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoSwap
open PASoundness.PAtoCompactIsoConditionalWrapper PASoundness.PAtoCompactIsoTransportWrapper
open PASoundness.PAtoCompactRestrictedInverseFirst
open PASoundness.PAtoCompactRestrictedInverseSecond
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The order conjunct extracted from the exact swapped target matrix. -/
def matrixOrder : Formula := match reverseMatrix7 with
  | .imp (.imp _ (.imp order .bottom)) .bottom => order
  | _ => .truth

/-- Restricted inverse correspondence and the forward matrix imply the
exact reversed order conjunct. -/
def matrix_order_clause : KDerivation
    (imp forwardMatrix.encode (imp restrictedInverseMatrix.encode matrixOrder.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [restrictedInverseMatrix.encode,forwardMatrix.encode]
  have hm : Context Γ forwardMatrix.encode := .hypothesis (by simp [Γ])
  have hi : Context Γ restrictedInverseMatrix.encode := Context.head _ _
  have ho : Context Γ orderFormula.encode := Context.conjunctionRight hm
  have hr : Context Γ PAtoCompactOrderIsoRestrictedGlobal.restrictedFamily.encode :=
    Context.conjunctionRight hi
  have hrev : Context Γ PAtoCompactOrderIsoRestrictedAll.restrictedReverseOrderAll :=
    .mp ho (.mp hr (.closed PAtoCompactOrderIsoRestrictedAll.restricted_reverse_order_all))
  exact .mp hrev (.closed PAtoCompactOrderIsoReverseAlpha.align_order_numeric)

/-- Given the explicit K proof of restricted inverse-matrix transfer, derive
symmetry under existence of a graph agreeing on pairs in the input domains.
No inverse graph is constructed by this wrapper. -/
def symmetry_of_matrix_step
    (step : KDerivation (imp forwardMatrix.encode
      (imp restrictedInverseMatrix.encode reverseMatrix7.encode))) :
    KDerivation (imp (allCode 6 (imp forwardMatrix.encode
      (existsCode 7 restrictedInverseMatrix.encode)))
      (imp equivalentFormula.encode reverseEquivalent.encode)) := by
  have ht := transport_exists 6 7 forwardMatrix restrictedInverseMatrix reverseMatrix7
    (by decide) (by decide) (by decide) step
  have ha := (CompactNamed.existentialAlpha 6 7 reverseMatrix
    (by decide) (by decide) (by decide)).2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [equivalentFormula.encode, allCode 6
    (imp forwardMatrix.encode (existsCode 7 restrictedInverseMatrix.encode))]
  have he : Context Γ equivalentFormula.encode := Context.head _ _
  have hi : Context Γ (allCode 6
      (imp forwardMatrix.encode (existsCode 7 restrictedInverseMatrix.encode))) := .hypothesis (by simp [Γ])
  have hr : Context Γ (existsCode 7 reverseMatrix7.encode) := .mp he (.mp hi (.closed ht))
  exact .mp hr (.closed ha)

/-- Combine the two guarded bijection-clause proofs and the guarded order
proof into the exact reverse matrix. -/
def matrix_step : KDerivation
    (imp forwardMatrix.encode (imp restrictedInverseMatrix.encode reverseMatrix7.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [restrictedInverseMatrix.encode,forwardMatrix.encode]
  have hm : Context Γ forwardMatrix.encode := .hypothesis (by simp [Γ])
  have hi : Context Γ restrictedInverseMatrix.encode := Context.head _ _
  have hl : Context Γ matrixFirst.encode :=
    .mp hi (.mp hm (.closed guarded_matrix_first_clause))
  have hr : Context Γ matrixSecond.encode :=
    .mp hi (.mp hm (.closed guarded_matrix_second_clause))
  have ho : Context Γ matrixOrder.encode := .mp hi (.mp hm (.closed matrix_order_clause))
  exact Context.conjunctionIntro (Context.conjunctionIntro hl hr) ho

/-- The original candidate is symmetric if each of its witness graphs has
a represented inverse agreeing on pairs in the two displayed domains. -/
def candidate_restricted_symmetry : KDerivation
    (imp (allCode 6 (imp forwardMatrix.encode (existsCode 7 restrictedInverseMatrix.encode)))
      (imp equivalentFormula.encode reverseEquivalent.encode)) :=
  symmetry_of_matrix_step matrix_step

theorem candidate_restricted_symmetry_certificate :
    theoremCode (certificate candidate_restricted_symmetry) =
      imp (allCode 6 (imp forwardMatrix.encode (existsCode 7 restrictedInverseMatrix.encode)))
        (imp equivalentFormula.encode reverseEquivalent.encode) :=
  certificate_correct candidate_restricted_symmetry

end PASoundness.PAtoCompactRestrictedSymmetry

#print axioms PASoundness.PAtoCompactRestrictedSymmetry.candidate_restricted_symmetry
#print axioms PASoundness.PAtoCompactRestrictedSymmetry.candidate_restricted_symmetry_certificate
