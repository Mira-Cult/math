import Shared.ComplexityBridge.TM2UnaryPolynomialIO
import Shared.ComplexityBridge.BoundedHardness

/-! Paid unary clock data for a proposed fixed-window SAT validator. The
outputs are canonical polynomial-time functions of the entire input list,
for each fixed verifier polynomial and finite slack. These are arithmetic
and complexity facts: they do not establish a validator, its actual number of
steps, a complete reduction, or a physical 284-state refinement. -/

namespace Shared.Beeping.NPcoNP.Source284SATWindowClock

open ComplexityTheory
open Shared.ComplexityBridge.BoundedHardness (commonFuel pairInputBound)
open Shared.ComplexityBridge.TM2UnaryPolynomialIO (unaryPolynomial unaryPolynomial_isPolyTime)

/-- One fixed polynomial for the common verifier fuel at witness bound `X`. -/
noncomputable def fuelPolynomial (clock : Polynomial Nat) : Polynomial Nat :=
  clock.comp (Polynomial.C 6 * Polynomial.X + Polynomial.C 1 + Polynomial.C 3 * Polynomial.X)

/-- The finite slack is included in the observed window, not only the outer
clock. This permits up to that many additional verifier steps without making
high certificate bits visible. -/
noncomputable def windowPolynomial (clock : Polynomial Nat) (slack : Nat) : Polynomial Nat :=
  fuelPolynomial clock + Polynomial.C 9 * Polynomial.X + Polynomial.C (slack + 1)

/-- Arithmetic allocation for scanning and rewinding one window, then
running the verifier. The constant and slack do not themselves prove the
operational schedule. -/
noncomputable def outerPolynomial (clock : Polynomial Nat) (slack : Nat) : Polynomial Nat :=
  Polynomial.C 2 * windowPolynomial clock slack + fuelPolynomial clock + Polynomial.C (slack + 3)

def verifierFuel (clock : Polynomial Nat) (x : List Bool) : Nat :=
  clock.eval (9*x.length+1)

def windowTokens (clock : Polynomial Nat) (slack : Nat) : List Bool → List Bool :=
  fun x => List.replicate (verifierFuel clock x + 9*x.length + slack + 1) true

def outerTokens (clock : Polynomial Nat) (slack : Nat) : List Bool → List Bool :=
  fun x => List.replicate (2*(windowTokens clock slack x).length +
    verifierFuel clock x + slack + 3) true

theorem verifierFuel_eq (clock : Polynomial Nat) (x : List Bool) :
    verifierFuel clock x = commonFuel Polynomial.X clock x := by
  simp [verifierFuel, commonFuel, pairInputBound, Polynomial.eval_X]
  congr 1
  omega

theorem fuel_eval (clock : Polynomial Nat) (x : List Bool) :
    (fuelPolynomial clock).eval x.length = commonFuel Polynomial.X clock x := by
  simp [fuelPolynomial, commonFuel, pairInputBound, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Nat.add_assoc]

theorem window_length (clock : Polynomial Nat) (slack : Nat) (x : List Bool) :
    (windowTokens clock slack x).length =
      commonFuel Polynomial.X clock x + 9*x.length + slack + 1 := by
  simp [windowTokens, verifierFuel_eq]

theorem outer_length (clock : Polynomial Nat) (slack : Nat) (x : List Bool) :
    (outerTokens clock slack x).length =
      2*(windowTokens clock slack x).length + commonFuel Polynomial.X clock x + slack + 3 := by
  simp [outerTokens, verifierFuel_eq]

theorem fuel_with_slack_le (clock : Polynomial Nat) (slack : Nat) (x : List Bool) :
    commonFuel Polynomial.X clock x + slack ≤ (windowTokens clock slack x).length := by
  rw [window_length]
  omega

theorem pair_bound_le (clock : Polynomial Nat) (slack : Nat) (x : List Bool) :
    9*x.length + 1 ≤ (windowTokens clock slack x).length := by
  rw [window_length]
  omega

theorem window_le_outer (clock : Polynomial Nat) (slack : Nat) (x : List Bool) :
    (windowTokens clock slack x).length ≤ (outerTokens clock slack x).length := by
  rw [outer_length]
  omega

theorem window_isPolyTime (clock : Polynomial Nat) (slack : Nat) :
    IsPolyTime (windowTokens clock slack) := by
  have he : unaryPolynomial (windowPolynomial clock slack) = windowTokens clock slack := by
    funext x
    simp [unaryPolynomial, windowPolynomial, windowTokens, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, fuel_eval,
      verifierFuel_eq, Nat.add_assoc]
  rw [← he]
  exact unaryPolynomial_isPolyTime (windowPolynomial clock slack)

theorem outer_isPolyTime (clock : Polynomial Nat) (slack : Nat) :
    IsPolyTime (outerTokens clock slack) := by
  have he : unaryPolynomial (outerPolynomial clock slack) = outerTokens clock slack := by
    funext x
    simp [unaryPolynomial, outerPolynomial, outerTokens, windowPolynomial,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      fuel_eval, verifierFuel_eq, window_length, Nat.add_assoc]
  rw [← he]
  exact unaryPolynomial_isPolyTime (outerPolynomial clock slack)

end Shared.Beeping.NPcoNP.Source284SATWindowClock
