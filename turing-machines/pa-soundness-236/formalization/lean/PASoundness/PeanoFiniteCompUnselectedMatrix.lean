import PASoundness.PeanoFiniteCompUnselectedRows
import PASoundness.PeanoFiniteComprehensionStepPackage

/-! The unselected successor matrix of bounded finite comprehension. -/
namespace PASoundness.PeanoFiniteCompUnselectedMatrix
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoFiniteComprehensionBase
open PeanoFiniteComprehensionStepPackage

/-- Given the old matrix and a false selector at n, PA derives the updated
matrix for the retained code and doubled power. This is one branch, not the
full successor implication or finite comprehension. -/
theorem unselected_matrix (φ : Peano.Formula) : FormulaProves
    ((matrix φ (.var 0)).imp
      ((selected φ).not.imp (updatedMatrix φ (.var 3)))) := by
  let M := matrix φ (.var 0)
  let N := (selected φ).not
  let Γ := [N,M]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hm : FOL.Context Peano.Axiom Γ M := .hypothesis (by simp [Γ])
  have hn : FOL.Context Peano.Axiom Γ N := .head _ _
  have hp : FOL.Context Peano.Axiom Γ (pow2 (.var 0) (.var 2)) :=
    FOL.Context.conjunctionLeft hm
  have hl : FOL.Context Peano.Axiom Γ (less (.var 3) (.var 2)) :=
    FOL.Context.conjunctionLeft (FOL.Context.conjunctionRight hm)
  have hr : FOL.Context Peano.Axiom Γ (rows φ (.var 0) (.var 3)) :=
    FOL.Context.conjunctionRight (FOL.Context.conjunctionRight hm)
  have hstep : FOL.Context Peano.Axiom Γ
      (pow2 (succ (.var 0)) newPower ⊓
        (less (.var 3) newPower ⊓ (bitFormula (.var 3) (.var 0)).not)) :=
    .mp (.mp (.closed PeanoFiniteCompUnselected.unselected_step) hp) hl
  have hnxt : FOL.Context Peano.Axiom Γ (pow2 (succ (.var 0)) newPower) :=
    FOL.Context.conjunctionLeft hstep
  have hbound : FOL.Context Peano.Axiom Γ (less (.var 3) newPower) :=
    FOL.Context.conjunctionLeft (FOL.Context.conjunctionRight hstep)
  have hrows : FOL.Context Peano.Axiom Γ (rows φ (succ (.var 0)) (.var 3)) :=
    .mp (.mp (.mp (.mp (.closed (PeanoFiniteCompUnselectedRows.unselected_rows φ)) hp) hl) hr) hn
  exact FOL.Context.conjunctionIntro hnxt (FOL.Context.conjunctionIntro hbound hrows)

end PASoundness.PeanoFiniteCompUnselectedMatrix

#print axioms PASoundness.PeanoFiniteCompUnselectedMatrix.unselected_matrix
