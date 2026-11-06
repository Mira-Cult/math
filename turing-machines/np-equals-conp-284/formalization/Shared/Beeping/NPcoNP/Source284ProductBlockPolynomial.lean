import Shared.Beeping.NPcoNP.Source284ReusableProductBlock
import Shared.Beeping.NPcoNP.Source284RectangularPolynomial

/-! The paid product-and-recycle table has an explicit polynomial clock
under polynomial bounds on its prepared blocks and payload width. -/
namespace Shared.Beeping.NPcoNP.Source284ProductBlockPolynomial

open Shared.Beeping.NPcoNP.Source284ReusableProductBlock

noncomputable def costPolynomial (outer inner width : Polynomial Nat) : Polynomial Nat :=
  Source284RectangularPolynomial.costPolynomial 2 outer inner 1 width+
    (2*(outer*inner)+2)*(4*width+7)

theorem costPolynomial_eval (n : Nat) (outer inner width : Polynomial Nat) :
    (costPolynomial outer inner width).eval n =
      (Source284RectangularPolynomial.costPolynomial 2 outer inner 1 width).eval n+
        (2*(outer.eval n*inner.eval n)+2)*(4*width.eval n+7) := by
  simp [costPolynomial,Polynomial.eval_add,Polynomial.eval_mul]

theorem cost_polynomial (n o i w : Nat) (outer inner width : Polynomial Nat)
    (ho : o ≤ outer.eval n) (hi : i ≤ inner.eval n) (hw : w ≤ width.eval n) :
    cost o i w ≤ (costPolynomial outer inner width).eval n := by
  have hp := Source284RectangularPolynomial.repeatCost_polynomial 2 n o i 1 w
    outer inner 1 width ho hi (by simp) hw
  have hc : Source284CounterTokenRecycle.cost (o*i) w ≤
      (2*(outer.eval n*inner.eval n)+2)*(4*width.eval n+7) := by
    unfold Source284CounterTokenRecycle.cost
    gcongr
  rw [costPolynomial_eval]
  unfold cost
  omega

end Shared.Beeping.NPcoNP.Source284ProductBlockPolynomial
