import PASoundness.PAtoCompactRestrictedForwardWitnessAll
import PASoundness.PAtoCompactRestrictedBackwardBijection
import PASoundness.PAtoCompactRestrictedOrderAll

/-! The full supplied-filter matrix for an isomorphism of old domains.
This is K proof data, not yet an existential graph or a quotient theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedMatrix
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactRestrictedForwardWitnessAll
open PASoundness.PAtoCompactRestrictedBackwardBijection
open PASoundness.PAtoCompactRestrictedOrderAll
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Both full one-to-one coverage clauses use the same supplied restricted
graph 8, with source 2 and target 5. -/
def forwardClause : Nat := allCode 7 (imp (member 2 7)
  (existsCode 3 PASoundness.PAtoCompactRestrictedForwardUnique.restrictedWitness.encode))

def backwardClause : Nat := allCode 3 (imp (member 5 3)
  (existsCode 7 PASoundness.PAtoCompactRestrictedBackwardWitness.restrictedWitness.encode))

/-- This exact explicit matrix has no quotient interpretation asserted. -/
def restrictedMatrix : Nat := both (both forwardClause backwardClause) restrictedOrder

/-- From two supplied successor graphs, the original isomorphism clauses,
their selected endpoint filter and the original top edge, K derives both
full restricted bijection clauses and the restricted order clause for the
same graph 8. Object values may coincide; the fixed syntactic labels avoid
their respective binders. Literal code 1 is `member 0 0`. -/
def restricted_matrix : KDerivation
    (imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp orderFormula.encode (imp PASoundness.PAtoCompactRestrictedOrderPoint.filter
        (imp (PASoundness.PAtoCompactOrderIsomorphism.graphFormula 6 2 5).encode
          (imp bijectionFormula.encode restrictedMatrix)))))) := by
  let SX := successorCode 2 0 9
  let SY := successorCode 5 1 10
  let O := orderFormula.encode
  let F := PASoundness.PAtoCompactRestrictedOrderPoint.filter
  let Top := (PASoundness.PAtoCompactOrderIsomorphism.graphFormula 6 2 5).encode
  let B := bijectionFormula.encode
  let Γ := [B,Top,F,O,SY,SX]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hb : Context Γ B := .head _ _
  have ht : Context Γ Top := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have hy : Context Γ SY := .hypothesis (by simp [Γ])
  have hx : Context Γ SX := .hypothesis (by simp [Γ])
  have hforward : Context Γ forwardClause :=
    .mp hb (.mp ht (.mp hf (.mp ho (.mp hy (.mp hx (.closed restricted_forward_witness_all))))))
  have hbackward : Context Γ backwardClause :=
    .mp ht (.mp hf (.mp hb (.mp ho (.mp hy (.mp hx (.closed backward_bijection))))))
  have horder : Context Γ restrictedOrder :=
    .mp hf (.mp ho (.mp hy (.mp hx (.closed restricted_order_all))))
  exact Context.conjunctionIntro (Context.conjunctionIntro hforward hbackward) horder

theorem restricted_matrix_certificate : theoremCode (certificate restricted_matrix) =
    imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp orderFormula.encode (imp PASoundness.PAtoCompactRestrictedOrderPoint.filter
        (imp (PASoundness.PAtoCompactOrderIsomorphism.graphFormula 6 2 5).encode
          (imp bijectionFormula.encode restrictedMatrix))))) :=
  certificate_correct restricted_matrix

end PASoundness.PAtoCompactRestrictedMatrix

#print axioms PASoundness.PAtoCompactRestrictedMatrix.restricted_matrix
#print axioms PASoundness.PAtoCompactRestrictedMatrix.restricted_matrix_certificate
