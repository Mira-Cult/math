import PASoundness.PeanoDivisionTotality

/-! Exposure of division witnesses at fixed fresh names for PA proof transport. -/
namespace PASoundness.PeanoDivisionWitnessElim
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoDivisionTotality

/-- Division row with dividend 5, modulus twice variable 2, quotient 9,
and remainder 10. -/
def matrix : Peano.Formula :=
  row (.var 5) (.var 9) (add (.var 2) (.var 2)) (.var 10)

/-- The capture-safe division formula uses exactly this pair of bound witnesses. -/
theorem division_syntax :
    division (.var 5) (add (.var 2) (.var 2)) =
      FOL.existsAt 9 (FOL.existsAt 10 matrix) := by
  simp [division, divisionTemplate, rows, row, matrix, FOL.existsAt, FOL.allAt,
    less, lessTemplate, exAt, v, Peano.add, Peano.mul, Peano.succ, Peano.zero,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux, Min.min]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

/-- Eliminate division's quotient and remainder from any PA derivation whose
conclusion does not contain either witness variable. -/
theorem division_elim (φ : Peano.Formula)
    (hf9 : 9 ∉ φ.freeVarFinset) (hf10 : 10 ∉ φ.freeVarFinset)
    (hrow : FormulaProves (matrix.imp φ)) :
    FormulaProves ((division (.var 5) (add (.var 2) (.var 2))).imp φ) := by
  rw [division_syntax]
  exact PeanoBitPositionReduction.exists_elim 9 hf9
    (PeanoBitPositionReduction.exists_elim 10 hf10 hrow)

end PASoundness.PeanoDivisionWitnessElim

#print axioms PASoundness.PeanoDivisionWitnessElim.division_elim
