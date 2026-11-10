import PASoundness.PeanoBetaCRTParameter

/-! PA projection of the bounded CRT invariant onto its actual row family.
The selected parameter and code remain under the same existential binders,
and the row relation and beta predicate share their original value witness.
No trace extension or power existence is asserted. -/
namespace PASoundness.PeanoBetaCRTProjection
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaCRTInvariant PeanoBetaCRTParameter

/-- A parameter and a single code witnessing the bounded row family. -/
def codedRows (φ : Peano.Formula) : Peano.Formula :=
  FOL.existsAt 1 (FOL.existsAt 9 (rowsAt φ (.var 8) 9))

private theorem fv_inf (φ ψ : Peano.Formula) :
    (φ ⊓ ψ).freeVarFinset = φ.freeVarFinset ∪ ψ.freeVarFinset := by
  change ((φ.imp ψ.not).not).freeVarFinset = _
  simp [FirstOrder.Language.BoundedFormula.freeVarFinset]

private theorem fv_exists (φ : Peano.Formula) (x : Nat) :
    (FOL.existsAt x φ).freeVarFinset = φ.freeVarFinset.erase x := by
  simp [FOL.existsAt, SyntaxTransport.allAt_freeVars,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]

/-- Discard the product, divisibility and future-inverse components of a
bounded solution. Freshness of product name 10 in φ is the only restriction;
φ may depend on the selected parameter 1 and selected code 9. -/
theorem bounded_solution_to_coded_rows (φ : Peano.Formula)
    (hφ10 : 10 ∉ φ.freeVarFinset) :
    FormulaProves ((boundedSolvedParameter φ).imp (codedRows φ)) := by
  let M := matrixAt φ (.var 8) 9 10
  let R := rowsAt φ (.var 8) 9
  let T := codedRows φ
  have hbody : FormulaProves (M.imp T) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have hm : FOL.Context Peano.Axiom [M] M := FOL.Context.head [] _
    have hr : FOL.Context Peano.Axiom [M] R :=
      FOL.Context.conjunctionLeft (FOL.Context.conjunctionLeft hm)
    have h9 : FormulaProves (R.imp (FOL.existsAt 9 R)) := by
      simpa only [SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom) R 9 (.var 9))
    have h1 : FormulaProves ((FOL.existsAt 9 R).imp T) := by
      simpa only [T, codedRows, R, SyntaxTransport.substAt_self] using
        (FOL.Derivation.existsIntro (A := Peano.Axiom) (FOL.existsAt 9 R) 1 (.var 1))
    exact .mp (.closed h1) (.mp (.closed h9) hr)
  have h9fresh : 9 ∉ T.freeVarFinset := by
    simp [T, codedRows, fv_exists]
  have h9elim := PeanoBitPositionReduction.exists_elim 9 h9fresh hbody
  have h10fresh : 10 ∉ T.freeVarFinset := by
    have ha : 10 ∉ (less (.var 2) (.var 8)).freeVarFinset := by decide
    have hb : 10 ∉ (beta (.var 9) (.var 1) (.var 2) (.var 3)).freeVarFinset := by decide
    simp [T, codedRows, rowsAt, fv_exists, fv_inf, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.freeVarFinset, hφ10, ha, hb]
  have h10elim := PeanoBitPositionReduction.exists_elim 10 h10fresh h9elim
  have hinv : FormulaProves ((invariantAt φ (.var 8)).imp T) := by
    simpa only [invariantAt, invariantWith, M] using h10elim
  let E := less (.var 16) (.var 1)
  have hbound : FormulaProves ((E ⊓ invariantAt φ (.var 8)).imp T) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    exact .mp (.closed hinv) (FOL.Context.conjunctionRight (FOL.Context.head [] _))
  have h1fresh : 1 ∉ T.freeVarFinset := by
    simp [T, codedRows, fv_exists]
  have h1elim := PeanoBitPositionReduction.exists_elim 1 h1fresh hbound
  simpa only [boundedSolvedParameter, E] using h1elim

end PASoundness.PeanoBetaCRTProjection

#print axioms PASoundness.PeanoBetaCRTProjection.bounded_solution_to_coded_rows
