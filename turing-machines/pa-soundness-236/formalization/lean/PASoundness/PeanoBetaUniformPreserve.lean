import PASoundness.PeanoDivisibility
import PASoundness.PeanoBetaCommonIncrement
import PASoundness.PeanoBitPositionReduction

/-! One bounded row-preservation step inside PA. The common increment's
bounded divisibility is an explicit hypothesis; it is not constructed here. -/
namespace PASoundness.PeanoBetaUniformPreserve
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic PeanoDivisibility

/-- The literal beta row at names 0,1,2,3. -/
def oldRow : Peano.Formula := beta (.var 0) (.var 1) (.var 2) (.var 3)
/-- The same row after adding the increment in name 4. -/
def newRow : Peano.Formula := beta (add (.var 0) (.var 4)) (.var 1) (.var 2) (.var 3)
/-- An explicit witness that the increment is a multiple of this row modulus. -/
def quotientEquation : Peano.Formula :=
  (.var 4 : Peano.Term).equal (mul (.var 5) (modulus (.var 1) (.var 2)))

private theorem divides_syntax :
    divides (modulus (.var 1) (.var 2)) (.var 4) = FOL.existsAt 5 quotientEquation := by
  simp [divides, dividesTemplate, quotientEquation, modulus, FOL.existsAt, FOL.allAt,
    Peano.mul, Peano.succ, Peano.zero, FirstOrder.Language.Term.equal,
    FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst,
    FirstOrder.Language.Term.relabel, FirstOrder.Language.BoundedFormula.not,
    FirstOrder.Language.BoundedFormula.subst, FirstOrder.Language.BoundedFormula.relabel,
    FirstOrder.Language.BoundedFormula.mapTermRel, FirstOrder.Language.BoundedFormula.relabelAux]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext j; fin_cases j <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

private theorem quotient_implies_preserve :
    FormulaProves (quotientEquation.imp (oldRow.imp newRow)) := by
  let Γ := [oldRow, quotientEquation]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom Γ quotientEquation :=
    FOL.Context.under (FOL.Context.head [] quotientEquation) oldRow
  have hr : FOL.Context Peano.Axiom Γ oldRow := FOL.Context.head _ _
  exact .mp (.mp (.closed (PeanoBetaCommonIncrement.beta_add_divisible
    (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5))) hr) he

/-- For the displayed variable names, a divisible increment preserves any
literal beta row. The divisor's existential quotient witness is eliminated
inside the PA proof, not selected using semantic arithmetic. -/
theorem divisible_row_preserved : FormulaProves
    ((divides (modulus (.var 1) (.var 2)) (.var 4)).imp (oldRow.imp newRow)) := by
  have hfresh : 5 ∉ (oldRow.imp newRow).freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 5 hfresh quotient_implies_preserve
  simpa only [divides_syntax] using h

/-- The named premise says each modulus at an index below name 6 divides the
increment in name 4. Names 0 and 1 hold the beta code and parameter. -/
def boundedDivisors : Peano.Formula :=
  FOL.allAt 2 ((less (.var 2) (.var 6)).imp
    (divides (modulus (.var 1) (.var 2)) (.var 4)))

/-- Under bounded divisibility, every row below the bound is preserved for
every value. The names in the statement are fixed explicitly; arbitrary-term
specialization and the construction of a suitable increment are separate. -/
theorem bounded_rows_preserved : FormulaProves
    (boundedDivisors.imp (FOL.allAt 2 (FOL.allAt 3
      ((less (.var 2) (.var 6)).imp (oldRow.imp newRow))))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.generalize 2
  · intro ψ hψ
    have h : ψ = boundedDivisors := by simpa using hψ
    subst ψ
    decide
  apply FOL.Context.generalize 3
  · intro ψ hψ
    have h : ψ = boundedDivisors := by simpa using hψ
    subst ψ
    decide
  apply FOL.Context.deduction
  let L := less (.var 2) (.var 6)
  let D := divides (modulus (.var 1) (.var 2)) (.var 4)
  let Γ := [L, boundedDivisors]
  have hbound : FOL.Context Peano.Axiom Γ boundedDivisors :=
    FOL.Context.under (FOL.Context.head [] boundedDivisors) L
  have hsmall : FOL.Context Peano.Axiom Γ L := FOL.Context.head _ _
  have hdiv : FOL.Context Peano.Axiom Γ D := .mp (FOL.Context.allSelf hbound) hsmall
  exact .mp (.closed divisible_row_preserved) hdiv

end PASoundness.PeanoBetaUniformPreserve
