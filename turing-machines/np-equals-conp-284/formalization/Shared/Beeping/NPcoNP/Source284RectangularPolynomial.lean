import Shared.Beeping.NPcoNP.Source284RectangularRepeat

/-! Explicit polynomial substitution for the paid rectangular token loop.
All bounds use ordinary natural-valued source transition counts. -/
namespace Shared.Beeping.NPcoNP.Source284RectangularPolynomial

open Shared.Beeping.NPcoNP.Source284RectangularRepeat

/-- The pass count is fixed in the program; the four component polynomials
bound the outer block, inner block, current counter and payload width. -/
noncomputable def costPolynomial (k : Nat) (outer inner current width : Polynomial Nat) : Polynomial Nat :=
  let finalCounter := current+Polynomial.C k*(outer*inner)
  Polynomial.C k * (outer*(3*inner*inner+inner*(2*finalCounter+4*width+33)+30)+
    (inner*inner+2)*outer*outer+8*inner+8*outer+26)

theorem costPolynomial_eval (k n : Nat) (outer inner current width : Polynomial Nat) :
    (costPolynomial k outer inner current width).eval n =
      k*roundUpper (outer.eval n) (inner.eval n)
        (current.eval n+k*(outer.eval n*inner.eval n)) (width.eval n) := by
  simp [costPolynomial,roundUpper,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C]

/-- Substitution into the charged table bound gives a single explicit
polynomial in the original input length. -/
theorem repeatCost_polynomial (k n o i c w : Nat)
    (outer inner current width : Polynomial Nat)
    (ho : o ≤ outer.eval n) (hi : i ≤ inner.eval n)
    (hc : c ≤ current.eval n) (hw : w ≤ width.eval n) :
    repeatCost k o i c w ≤ (costPolynomial k outer inner current width).eval n := by
  rw [costPolynomial_eval]
  apply le_trans (repeatCost_le k o i c w)
  unfold roundUpper
  gcongr

end Shared.Beeping.NPcoNP.Source284RectangularPolynomial
