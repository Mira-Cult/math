import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactZeroSuccessor
import PASoundness.CompactQuantifiers

/-! Capture-safe K transport from a supplied isomorphism matrix to the
reflexive candidate formula on name 30. The matrix and equality aliases remain
explicit hypotheses; graph existence and quotient reflexivity are not proved. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalReflexiveMatrixTransport
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor

/-- The exact literal candidate formula with both endpoint names replaced by
30; all original binder labels are retained. -/
def reflexive30 : CompactNamed.Formula :=
  CompactNamed.replace 1 30 (CompactNamed.replace 0 30 equivalentFormula)

/-- An explicitly supplied matrix yields E(0,1), using graph name 6 as the
existential witness. -/
def matrix_to_equivalent : KDerivation
    (imp (both bijectionFormula.encode orderFormula.encode) equivalentFormula.encode) := by
  let f := namedBoth bijectionFormula orderFormula
  have hi := CompactNamed.existsIntroduce 6 f (by decide)
  exact hi

/-- The given equality aliases transport a supplied matrix to the concrete
reflexive candidate E(30,30), retaining existential graph binding. -/
def matrix_to_reflexive : KDerivation
    (imp (equal 0 30) (imp (equal 1 30)
      (imp (both bijectionFormula.encode orderFormula.encode) reflexive30.encode))) := by
  have h0 := (CompactNamed.equalityReplace 0 30 equivalentFormula (by decide) (by decide)).1
  have h1 := (CompactNamed.equalityReplace 1 30 (CompactNamed.replace 0 30 equivalentFormula)
    (by decide) (by decide)).1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let M := both bijectionFormula.encode orderFormula.encode
  let Γ := [M,equal 1 30,equal 0 30]
  have hzero : Context Γ (equal 0 30) := .hypothesis (by simp [Γ])
  have hone : Context Γ (equal 1 30) := .hypothesis (by simp [Γ])
  have hm : Context Γ M := Context.head _ _
  have hE : Context Γ equivalentFormula.encode := .mp hm (.closed matrix_to_equivalent)
  have hE0 : Context Γ (CompactNamed.replace 0 30 equivalentFormula).encode :=
    .mp hE (.mp hzero (.closed h0))
  exact .mp hE0 (.mp hone (.closed h1))

theorem matrix_to_reflexive_certificate : theoremCode (certificate matrix_to_reflexive) =
    imp (equal 0 30) (imp (equal 1 30)
      (imp (both bijectionFormula.encode orderFormula.encode) reflexive30.encode)) :=
  certificate_correct matrix_to_reflexive

end PASoundness.PAtoCompactDiagonalReflexiveMatrixTransport

#print axioms PASoundness.PAtoCompactDiagonalReflexiveMatrixTransport.matrix_to_equivalent
#print axioms PASoundness.PAtoCompactDiagonalReflexiveMatrixTransport.matrix_to_reflexive
#print axioms PASoundness.PAtoCompactDiagonalReflexiveMatrixTransport.matrix_to_reflexive_certificate
