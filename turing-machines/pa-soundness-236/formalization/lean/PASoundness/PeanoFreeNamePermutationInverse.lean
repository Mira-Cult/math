import PASoundness.PeanoFreeNamePermutation

/-! Inverse of a finite list of free-name swaps. -/
namespace PASoundness.PeanoFreeNamePermutationInverse
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoFreeNamePermutation

/-- Applying a concatenation acts left to right. -/
theorem applyName_append (xs ys : List (Nat × Nat)) (n : Nat) :
    applyName (xs ++ ys) n = applyName ys (applyName xs n) := by
  induction xs generalizing n with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨x,y⟩
    exact ih _

private theorem swap_involution (x y n : Nat) :
    (if (if n = x then y else if n = y then x else n) = x then y
      else if (if n = x then y else if n = y then x else n) = y then x
      else (if n = x then y else if n = y then x else n)) = n := by
  by_cases hx : n = x <;> by_cases hy : n = y <;> simp_all

/-- Reversing the swap sequence yields the inverse finite name action. -/
theorem reverse_applyName (xs : List (Nat × Nat)) (n : Nat) :
    applyName xs.reverse (applyName xs n) = n := by
  induction xs generalizing n with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨x,y⟩
    simp only [List.reverse_cons, applyName, applyName_append, ih]
    exact swap_involution x y n

/-- The action of any finite swap list is injective. -/
theorem applyName_injective (xs : List (Nat × Nat)) : Function.Injective (applyName xs) := by
  intro a b h
  have := congrArg (applyName xs.reverse) h
  simpa only [reverse_applyName] using this

/-- The exact formula is recovered after the forward and inverse free-name
permutations. This is a syntax identity, not AX8 or its interpretation. -/
theorem reverse_applyFormula (xs : List (Nat × Nat)) (φ : Peano.Formula) :
    applyFormula xs.reverse (applyFormula xs φ) = φ := by
  rw [applyFormula_eq, applyFormula_eq, SyntaxTransport.formula_subst_comp]
  have hsub : (fun n => ((.var (applyName xs n)) : Peano.Term).subst
      (fun x => .var (applyName xs.reverse x))) = Term.var := by
    funext n
    simp only [FirstOrder.Language.Term.subst, reverse_applyName]
  rw [hsub, SyntaxTransport.formula_subst_var]

end PASoundness.PeanoFreeNamePermutationInverse

#print axioms PASoundness.PeanoFreeNamePermutationInverse.reverse_applyName
#print axioms PASoundness.PeanoFreeNamePermutationInverse.reverse_applyFormula
