import PASoundness.PeanoPowerOldUnpack
import PASoundness.PeanoBetaAppendBase
import PASoundness.PeanoBetaAppendRowsExist
import PASoundness.PeanoBetaAppendFullFamily
import PASoundness.PeanoPowerAppendAlpha

/-! The successor-power trace from a supplied fixed-name old trace matrix.
The same newly constructed parameter and code are used for every new row. -/
namespace PASoundness.PeanoPowerAppendSuccessor
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoPowerOldUnpack PeanoBetaAppendTraceFamily
open PeanoBetaAppendRowsExist PeanoBetaAppendFullFamily

/-- From a fixed old code with its literal complete doubling trace, PA
constructs the next literal power trace. The old code and parameter remain
free; the newly constructed code and parameter are existentially eliminated. -/
theorem successor_from_old_matrix : FormulaProves
    (oldMatrix.imp (pow2 (succ (.var 0)) (add (.var 6) (.var 6)))) := by
  let M := oldMatrix
  let R := recodedRows
  let T := pow2 (succ (.var 0)) (add (.var 6) (.var 6))
  have hlocal : FormulaProves (R.imp (M.imp T)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [M,R]
    have hm : FOL.Context Peano.Axiom Γ M := FOL.Context.head _ _
    have hr : FOL.Context Peano.Axiom Γ R := .hypothesis (by simp [Γ])
    have hz : FOL.Context Peano.Axiom Γ (beta (.var 4) (.var 5) zero (succ zero)) :=
      FOL.Context.conjunctionLeft hm
    have he : FOL.Context Peano.Axiom Γ (beta (.var 4) (.var 5) (.var 0) (.var 6)) :=
      FOL.Context.conjunctionLeft (FOL.Context.conjunctionRight hm)
    have hf : FOL.Context Peano.Axiom Γ PeanoBetaAppendTraceFamily.oldFamily :=
      FOL.Context.conjunctionRight (FOL.Context.conjunctionRight hm)
    have hnewz : FOL.Context Peano.Axiom Γ (beta (.var 9) (.var 1) zero (succ zero)) :=
      .mp (.mp (.closed PeanoBetaAppendBase.initial_row_preserved) hr) hz
    have hnewf : FOL.Context Peano.Axiom Γ PeanoPowerAppendAlpha.highFamily := by
      exact .mp (.mp (.mp (.closed PeanoBetaAppendFullFamily.full_family_preserved) hf) hr) he
    have hnewe : FOL.Context Peano.Axiom Γ
        (beta (.var 9) (.var 1) (succ (.var 0)) (add (.var 6) (.var 6))) :=
      .mp (.mp (.closed PeanoBetaAppendEndFamily.appended_output) hr) he
    exact .mp (.mp (.mp (.closed PeanoPowerAppendAlpha.family_to_power) hnewf) hnewz) hnewe
  have hfree9 : 9 ∉ (M.imp T).freeVarFinset := by decide
  have h9 := PeanoBitPositionReduction.exists_elim 9 hfree9 hlocal
  have hfree1 : 1 ∉ (M.imp T).freeVarFinset := by decide
  have h1 := PeanoBitPositionReduction.exists_elim 1 hfree1 h9
  have hex : FormulaProves (FOL.existsAt 1 (FOL.existsAt 9 R)) := by
    simpa only [R, recodedRows, PeanoBetaAppendRowsExist.appendedRows,
      PeanoBetaAppendCRT.endIndex] using PeanoBetaAppendRowsExist.append_rows_exist
  exact .mp h1 hex

/-- PA extends any literal power trace by one doubling step. The old code and
parameter are unpacked and eliminated without changing the final formula. -/
theorem power_successor : FormulaProves
    ((pow2 (.var 0) (.var 6)).imp
      (pow2 (succ (.var 0)) (add (.var 6) (.var 6)))) := by
  let T := pow2 (succ (.var 0)) (add (.var 6) (.var 6))
  have hf5 : 5 ∉ T.freeVarFinset := by decide
  have h5 := PeanoBitPositionReduction.exists_elim 5 hf5 successor_from_old_matrix
  have hf4 : 4 ∉ T.freeVarFinset := by decide
  have h4 := PeanoBitPositionReduction.exists_elim 4 hf4 h5
  exact FOL.Derivation.compose PeanoPowerOldUnpack.old_power_unpack h4

end PASoundness.PeanoPowerAppendSuccessor

#print axioms PASoundness.PeanoPowerAppendSuccessor.successor_from_old_matrix
#print axioms PASoundness.PeanoPowerAppendSuccessor.power_successor
