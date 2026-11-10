import PASoundness.PeanoFiniteComprehensionBase
import PASoundness.PeanoBetaCRTPrefixSubst

/-! Capture-safe induction substitutions for the bounded comprehension
invariant. These syntax equalities do not establish the induction step or
finite comprehension. -/
namespace PASoundness.PeanoFiniteComprehensionSubst
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoFiniteComprehensionBase PeanoBetaCRTPrefixSubst.Syntax

private theorem subst_imp (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ.imp ψ) x t = (FOL.substAt φ x t).imp (FOL.substAt ψ x t) := rfl

private theorem subst_and (φ ψ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    FOL.substAt (φ ⊓ ψ) x t = (FOL.substAt φ x t) ⊓ (FOL.substAt ψ x t) := rfl

private theorem bit_fresh (t : Peano.Term) : FOL.substAt
    (bitFormula (.var 3) (.var 1)) 0 t = bitFormula (.var 3) (.var 1) := by
  apply substAt_of_fresh
  decide

private theorem bound_fresh (t : Peano.Term) : FOL.substAt
    (less (.var 3) (.var 2)) 0 t = less (.var 3) (.var 2) := by
  apply substAt_of_fresh
  decide

private theorem less_zero : FOL.substAt (less (.var 1) (.var 0)) 0 zero =
    less (.var 1) zero := by
  simp [FOL.substAt, less_subst, FirstOrder.Language.Term.subst]

private theorem less_succ : FOL.substAt (less (.var 1) (.var 0)) 0 (succ (.var 0)) =
    less (.var 1) (succ (.var 0)) := by
  simp [FOL.substAt, less_subst, FirstOrder.Language.Term.subst]

private theorem pow_zero : FOL.substAt (pow2 (.var 0) (.var 2)) 0 zero =
    pow2 zero (.var 2) := by
  simp [FOL.substAt, pow2_subst, FirstOrder.Language.Term.subst]

private theorem pow_succ : FOL.substAt (pow2 (.var 0) (.var 2)) 0 (succ (.var 0)) =
    pow2 (succ (.var 0)) (.var 2) := by
  simp [FOL.substAt, pow2_subst, FirstOrder.Language.Term.subst]

theorem rows_zero (φ : Peano.Formula) (hφ : 0 ∉ φ.freeVarFinset) :
    FOL.substAt (rows φ (.var 0) (.var 3)) 0 zero = rows φ zero (.var 3) := by
  unfold rows
  rw [subst_zero_allAt _ 0 1 (by decide), subst_imp, less_zero, subst_and,
    subst_imp, subst_imp, bit_fresh, substAt_of_fresh φ 0 zero hφ]

theorem rows_succ (φ : Peano.Formula) (hφ : 0 ∉ φ.freeVarFinset) :
    FOL.substAt (rows φ (.var 0) (.var 3)) 0 (succ (.var 0)) =
      rows φ (succ (.var 0)) (.var 3) := by
  unfold rows
  rw [subst_succSelf_allAt _ 0 1 (by decide), subst_imp, less_succ, subst_and,
    subst_imp, subst_imp, bit_fresh, substAt_of_fresh φ 0 (succ (.var 0)) hφ]

theorem matrix_zero (φ : Peano.Formula) (hφ : 0 ∉ φ.freeVarFinset) :
    FOL.substAt (matrix φ (.var 0)) 0 zero = matrix φ zero := by
  unfold matrix
  rw [subst_and, subst_and, pow_zero, bound_fresh, rows_zero φ hφ]

theorem matrix_succ (φ : Peano.Formula) (hφ : 0 ∉ φ.freeVarFinset) :
    FOL.substAt (matrix φ (.var 0)) 0 (succ (.var 0)) = matrix φ (succ (.var 0)) := by
  unfold matrix
  rw [subst_and, subst_and, pow_succ, bound_fresh, rows_succ φ hφ]

/-- At zero the code, power, and row binders retain their original roles. -/
theorem invariant_zero (φ : Peano.Formula) (hφ : 0 ∉ φ.freeVarFinset) :
    FOL.substAt (invariant φ (.var 0)) 0 zero = invariant φ zero := by
  unfold invariant
  rw [subst_zero_existsAt _ 0 2 (by decide), subst_zero_existsAt _ 0 3 (by decide),
    matrix_zero φ hφ]

/-- The successor substitution leaves φ unchanged under its stated freshness. -/
theorem invariant_succ (φ : Peano.Formula) (hφ : 0 ∉ φ.freeVarFinset) :
    FOL.substAt (invariant φ (.var 0)) 0 (succ (.var 0)) = invariant φ (succ (.var 0)) := by
  unfold invariant
  rw [subst_succSelf_existsAt _ 0 2 (by decide), subst_succSelf_existsAt _ 0 3 (by decide),
    matrix_succ φ hφ]

end PASoundness.PeanoFiniteComprehensionSubst

#print axioms PASoundness.PeanoFiniteComprehensionSubst.invariant_zero
#print axioms PASoundness.PeanoFiniteComprehensionSubst.invariant_succ
