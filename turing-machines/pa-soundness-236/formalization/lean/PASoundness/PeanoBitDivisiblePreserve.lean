import PASoundness.PeanoBitMultiplePreserveAll
import PASoundness.PeanoDivisibility

/-! Eliminate an explicit divisibility witness to preserve a set bit. -/
namespace PASoundness.PeanoBitDivisiblePreserve
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoDivisibility

private def quotientRow : Peano.Formula :=
  (.var 6 : Peano.Term).equal (mul (.var 7) (add (.var 2) (.var 2)))

private theorem divides_syntax :
    divides (add (.var 2) (.var 2)) (.var 6) = FOL.existsAt 7 quotientRow := by
  simp [divides, dividesTemplate, quotientRow, FOL.existsAt, FOL.allAt,
    Peano.mul, Peano.add, Peano.zero, FirstOrder.Language.Term.equal,
    FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst,
    FirstOrder.Language.Term.relabel, FirstOrder.Language.BoundedFormula.not,
    FirstOrder.Language.BoundedFormula.subst, FirstOrder.Language.BoundedFormula.relabel,
    FirstOrder.Language.BoundedFormula.mapTermRel, FirstOrder.Language.BoundedFormula.relabelAux]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

/-- From an actual divisibility premise, PA preserves a set bit when the
increment is added. This is the forward direction; neither divisibility nor
reverse preservation is asserted here. -/
theorem preserve_bit_of_divides : FormulaProves
    ((divides (add (.var 2) (.var 2)) (.var 6)).imp
      ((pow2 (.var 1) (.var 2)).imp
        ((bitFormula (.var 5) (.var 1)).imp
          (bitFormula (add (.var 5) (.var 6)) (.var 1))))) := by
  let P := pow2 (.var 1) (.var 2)
  let B := bitFormula (.var 5) (.var 1)
  let T := bitFormula (add (.var 5) (.var 6)) (.var 1)
  let G := P.imp (B.imp T)
  have hr : FormulaProves (quotientRow.imp G) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [B,P,quotientRow]
    have hb : FOL.Context Peano.Axiom Γ B := .head _ _
    have hp : FOL.Context Peano.Axiom Γ P := .hypothesis (by simp [Γ])
    have he : FOL.Context Peano.Axiom Γ quotientRow := .hypothesis (by simp [Γ])
    exact .mp (.mp (.mp (.closed (PeanoBitMultiplePreserveAll.preserve_bit_multiple_all
      (.var 5) (.var 1) (.var 6) (.var 2) (.var 7))) hb) hp) he
  have hf : 7 ∉ G.freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 7 hf hr
  simpa only [divides_syntax, G, P, B, T] using h

end PASoundness.PeanoBitDivisiblePreserve

#print axioms PASoundness.PeanoBitDivisiblePreserve.preserve_bit_of_divides
