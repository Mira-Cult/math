import Shared.Beeping.NPcoNP.Source284RawProductIteration

/-! For a fixed number of stages, both block sizes are explicit polynomials
in the initial block sizes. -/
namespace Shared.Beeping.NPcoNP.Source284ProductIterationPolynomial

open Shared.Beeping.NPcoNP.Source284ProductIteration

noncomputable def outerPolynomial : Nat → Polynomial Nat → Polynomial Nat → Polynomial Nat
  | 0, a, _ => a
  | k+1, a, b => outerPolynomial k b (a*b)

noncomputable def innerPolynomial : Nat → Polynomial Nat → Polynomial Nat → Polynomial Nat
  | 0, _, b => b
  | k+1, a, b => innerPolynomial k b (a*b)

theorem outer_eval (k n : Nat) (a b : Polynomial Nat) :
    (outerPolynomial k a b).eval n = outerAfter k (a.eval n) (b.eval n) := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih => simpa [outerPolynomial,outerAfter,Polynomial.eval_mul] using ih b (a*b)

theorem inner_eval (k n : Nat) (a b : Polynomial Nat) :
    (innerPolynomial k a b).eval n = innerAfter k (a.eval n) (b.eval n) := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih => simpa [innerPolynomial,innerAfter,Polynomial.eval_mul] using ih b (a*b)

/-- This is the exact size of the newest block produced from raw length `n`. -/
noncomputable def rawBlockPolynomial (k : Nat) : Polynomial Nat :=
  innerPolynomial k Polynomial.X Polynomial.X

theorem rawBlockPolynomial_eval (k n : Nat) :
    (rawBlockPolynomial k).eval n = innerAfter k n n := by
  simpa [rawBlockPolynomial] using inner_eval k n Polynomial.X Polynomial.X

end Shared.Beeping.NPcoNP.Source284ProductIterationPolynomial
