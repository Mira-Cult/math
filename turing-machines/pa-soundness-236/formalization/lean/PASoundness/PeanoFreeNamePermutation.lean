import PASoundness.PeanoFreeNameSwap

/-! Explicit finite sequences of free-name swaps preserve PA derivability. -/
namespace PASoundness.PeanoFreeNamePermutation
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic

/-- Apply the named swaps left to right to a free variable. -/
def applyName : List (Nat × Nat) → Nat → Nat
  | [], n => n
  | (x,y) :: rest, n => applyName rest (if n = x then y else if n = y then x else n)

/-- Apply the same swaps as capture-safe substitutions to a formula. -/
def applyFormula : List (Nat × Nat) → Peano.Formula → Peano.Formula
  | [], φ => φ
  | (x,y) :: rest, φ => applyFormula rest (φ.subst (PeanoFreeNameSwap.swapName x y))

/-- Iterated single-name swaps agree with the simultaneous action of the
displayed finite name permutation on the formula's free variables. -/
theorem applyFormula_eq (xs : List (Nat × Nat)) (φ : Peano.Formula) :
    applyFormula xs φ = φ.subst (fun n => .var (applyName xs n)) := by
  induction xs generalizing φ with
  | nil => simp [applyFormula, applyName, SyntaxTransport.formula_subst_var]
  | cons pair rest ih =>
    rcases pair with ⟨x,y⟩
    rw [applyFormula, ih, SyntaxTransport.formula_subst_comp]
    congr 1
    funext n
    by_cases hxy : x = y
    · subst y
      by_cases hx : n = x <;>
        simp [PeanoFreeNameSwap.swapName, applyName, hx, FirstOrder.Language.Term.subst]
    · by_cases hx : n = x <;> by_cases hy : n = y <;>
        simp [PeanoFreeNameSwap.swapName, applyName, hx, hy, Ne.symm hxy,
          FirstOrder.Language.Term.subst]

/-- Any finite sequence of swaps transforms actual PA proof data without
assuming semantic truth or a substitution theorem for arithmetic axioms. -/
theorem applyFormula_proves (xs : List (Nat × Nat)) (φ : Peano.Formula)
    (h : FormulaProves φ) : FormulaProves (applyFormula xs φ) := by
  induction xs generalizing φ with
  | nil => exact h
  | cons pair rest ih =>
    rcases pair with ⟨x,y⟩
    exact ih _ (PeanoFreeNameSwap.swap_proves φ x y h)

/-- Equivalently, the corresponding simultaneous free-variable permutation
preserves PA derivability. The caller must still construct the swap list and
prove any desired freshness and alignment properties. -/
theorem permute_proves (xs : List (Nat × Nat)) (φ : Peano.Formula)
    (h : FormulaProves φ) :
    FormulaProves (φ.subst (fun n => .var (applyName xs n))) := by
  rw [← applyFormula_eq]
  exact applyFormula_proves xs φ h

end PASoundness.PeanoFreeNamePermutation

#print axioms PASoundness.PeanoFreeNamePermutation.permute_proves
