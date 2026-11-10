import PASoundness.PAtoCompactSuccCongruenceData
import PASoundness.CompactFreshen

/-! Capture-safe K vacuity of the old isomorphism matrix at name 2, despite
2 being bound within both clauses. Freshening provides only syntactic proof
transport; no semantic soundness or quotient property is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccOldMatrixVacuity
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuccCongruenceData
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def oldMatrixFormula : Formula := namedBoth bijectionFormula orderFormula

theorem old_matrix_encode : oldMatrixFormula.encode = oldMatrix := rfl

private theorem matrix_names_lt : ∀ v ∈ oldMatrixFormula.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ oldMatrixFormula.names.sup id at hm
  have hb : oldMatrixFormula.names.sup id < 30 := by decide
  omega

def freshOldMatrix := freshen oldMatrixFormula 30 matrix_names_lt

theorem fresh_matrix_2 : 2 ∉ freshOldMatrix.formula.names := by decide

/-- The exact old matrix entails its universal closure in the bound name 2. -/
def old_matrix_vacuity : KDerivation (imp oldMatrix (allCode 2 oldMatrix)) := by
  have hr : KDerivation (imp oldMatrixFormula.encode (allCode 2 oldMatrixFormula.encode)) :=
    compose freshOldMatrix.equivalent.forward
      (compose (freshOldMatrix.formula.vacuity 2 fresh_matrix_2)
        (allCongr 2 freshOldMatrix.equivalent.backward))
  simpa only [old_matrix_encode] using hr

theorem old_matrix_vacuity_certificate : theoremCode (certificate old_matrix_vacuity) =
    imp oldMatrix (allCode 2 oldMatrix) := certificate_correct old_matrix_vacuity

end PASoundness.PAtoCompactSuccOldMatrixVacuity

#print axioms PASoundness.PAtoCompactSuccOldMatrixVacuity.old_matrix_vacuity
#print axioms PASoundness.PAtoCompactSuccOldMatrixVacuity.old_matrix_vacuity_certificate
