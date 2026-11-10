import PASoundness.PeanoFiniteComprehensionStepPackage
import PASoundness.PeanoFiniteCompSelectedRows

/-! The selected branch constructs the complete successor matrix using the
same old power and code. Existential packaging is a separate theorem. -/
namespace PASoundness.PeanoFiniteCompSelectedMatrix
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoFiniteComprehensionBase
open PeanoFiniteComprehensionStepPackage

/-- From the current matrix and the selected predicate at n, PA derives the
entire next matrix with p'=p+p and a'=p+a. The relation remains unchanged. -/
theorem selected_matrix (φ : Peano.Formula) : FormulaProves
    ((matrix φ (.var 0)).imp ((selected φ).imp (updatedMatrix φ chosenCode))) := by
  let M := matrix φ (.var 0)
  let S := selected φ
  let P := pow2 (.var 0) (.var 2)
  let B := less (.var 3) (.var 2)
  let R := rows φ (.var 0) (.var 3)
  let Γ := [S,M]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hm : FOL.Context Peano.Axiom Γ M := .hypothesis (by simp [Γ])
  have hs : FOL.Context Peano.Axiom Γ S := FOL.Context.head _ _
  have hp : FOL.Context Peano.Axiom Γ P := FOL.Context.conjunctionLeft hm
  have hb : FOL.Context Peano.Axiom Γ B :=
    FOL.Context.conjunctionLeft (FOL.Context.conjunctionRight hm)
  have hr : FOL.Context Peano.Axiom Γ R :=
    FOL.Context.conjunctionRight (FOL.Context.conjunctionRight hm)
  have hprop : FOL.Context Peano.Axiom Γ
      (pow2 (succ (.var 0)) newPower ⊓
        (less chosenCode newPower ⊓ bitFormula chosenCode (.var 0))) :=
    .mp (.mp (.closed PeanoFiniteComprehensionSelected.selected_code_properties) hp) hb
  have hrows : FOL.Context Peano.Axiom Γ (rows φ (succ (.var 0)) chosenCode) :=
    .mp (.mp (.mp (.mp (.closed (PeanoFiniteCompSelectedRows.selected_rows φ)) hp) hb) hr) hs
  exact FOL.Context.conjunctionIntro (FOL.Context.conjunctionLeft hprop)
    (FOL.Context.conjunctionIntro
      (FOL.Context.conjunctionLeft (FOL.Context.conjunctionRight hprop)) hrows)

end PASoundness.PeanoFiniteCompSelectedMatrix

#print axioms PASoundness.PeanoFiniteCompSelectedMatrix.selected_matrix
