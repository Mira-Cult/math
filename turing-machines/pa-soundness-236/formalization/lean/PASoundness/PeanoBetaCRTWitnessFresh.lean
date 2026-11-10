import PASoundness.PeanoBetaCRTInvariant

/-! Syntactic freshness of selected-witness names in the current and next CRT
invariants. The arbitrary relation must itself omit the relevant witness name. -/
namespace PASoundness.PeanoBetaCRTWitnessFresh
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic PeanoDivisibility
open PeanoBetaCRTInvariant

private theorem fv_inf (φ ψ : Peano.Formula) :
    (φ ⊓ ψ).freeVarFinset = φ.freeVarFinset ∪ ψ.freeVarFinset := by
  change ((φ.imp ψ.not).not).freeVarFinset = _
  simp [FirstOrder.Language.BoundedFormula.freeVarFinset]

private theorem fv_exists (φ : Peano.Formula) (x : Nat) :
    (FOL.existsAt x φ).freeVarFinset = φ.freeVarFinset.erase x := by
  simp [FOL.existsAt, SyntaxTransport.allAt_freeVars,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]

/-- Selected witness names 13,14,15 are fresh in the current matrix whenever
they are fresh in the arbitrary row relation φ. -/
theorem current_fresh (φ : Peano.Formula) (x : Nat)
    (hx : x = 13 ∨ x = 14 ∨ x = 15) (hφ : x ∉ φ.freeVarFinset) :
    x ∉ (currentMatrix φ).freeVarFinset := by
  have ha : x ∉ (less (.var 2) (.var 7)).freeVarFinset := by
    rcases hx with rfl | rfl | rfl <;> decide
  have hb : x ∉ (beta (.var 9) (.var 1) (.var 2) (.var 3)).freeVarFinset := by
    rcases hx with rfl | rfl | rfl <;> decide
  have hc : x ∉ (divides (modulus (.var 1) (.var 2)) (.var 10)).freeVarFinset := by
    rcases hx with rfl | rfl | rfl <;> decide
  have hd : x ∉ (less (.var 2) (.var 8)).freeVarFinset := by
    rcases hx with rfl | rfl | rfl <;> decide
  have he : x ∉ (((mul (.var 10) (.var 3)).equal
    (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2)))) : Peano.Formula)).freeVarFinset := by
    rcases hx with rfl | rfl | rfl <;> decide
  simp [currentMatrix, matrixAt, rowsAt, factorsAt, futureAt, fv_inf, fv_exists,
    SyntaxTransport.allAt_freeVars, FirstOrder.Language.BoundedFormula.not,
    FirstOrder.Language.BoundedFormula.freeVarFinset, hφ, ha, hb, hc, hd, he]

/-- The selected-witness names do not occur freely in the next invariant,
provided the target relation itself does not use that name. -/
theorem next_fresh (φ : Peano.Formula) (x : Nat)
    (hx : x = 13 ∨ x = 14 ∨ x = 15) (hφ : x ∉ φ.freeVarFinset) :
    x ∉ (nextInvariant φ).freeVarFinset := by
  have ha : x ∉ (less (.var 2) (succ (.var 7))).freeVarFinset := by
    rcases hx with rfl | rfl | rfl <;> decide
  have hb : x ∉ (beta (.var 11) (.var 1) (.var 2) (.var 3)).freeVarFinset := by
    rcases hx with rfl | rfl | rfl <;> decide
  have hc : x ∉ (divides (modulus (.var 1) (.var 2)) (.var 12)).freeVarFinset := by
    rcases hx with rfl | rfl | rfl <;> decide
  have hd : x ∉ (less (.var 2) (.var 8)).freeVarFinset := by
    rcases hx with rfl | rfl | rfl <;> decide
  have he : x ∉ (((mul (.var 12) (.var 3)).equal
      (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2)))) : Peano.Formula)).freeVarFinset := by
    rcases hx with rfl | rfl | rfl <;> decide
  have hne2 : x ≠ 2 := by rcases hx with rfl | rfl | rfl <;> decide
  have hne3 : x ≠ 3 := by rcases hx with rfl | rfl | rfl <;> decide
  have hne4 : x ≠ 4 := by rcases hx with rfl | rfl | rfl <;> decide
  have hne11 : x ≠ 11 := by rcases hx with rfl | rfl | rfl <;> decide
  have hne12 : x ≠ 12 := by rcases hx with rfl | rfl | rfl <;> decide
  simp [nextInvariant, nextMatrix, nextRows, nextFactors, nextFuture, rowsAt,
    factorsAt, futureAt, fv_exists, fv_inf, SyntaxTransport.allAt_freeVars,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset,
    hφ, ha, hb, hc, hd, he, hne2, hne3, hne4, hne11, hne12]


end PASoundness.PeanoBetaCRTWitnessFresh
