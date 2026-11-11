import Sude.FWUniformStockFloor
import Mathlib.Algebra.Order.Floor.Semiring

/-! A floor-safe sufficient condition for FW's natural-subtraction gate. -/
namespace Sude
noncomputable section

/-- A 16-unit rounding allowance converts a real stock margin into the
strict square gate used by the FW physical supply. The subtraction on the
right is natural-number subtraction, including its truncation at zero. -/
theorem fw_floor_stock_square_gate (X stock : ℝ) (B : ℕ) (hX : 0 ≤ X)
    (hmargin : (B : ℝ) + 16 + 4 * Real.sqrt X ≤ 16 * stock) :
    16 * X < (((16 * ⌊stock⌋₊ - B : ℕ) : ℝ) ^ 2) := by
  have hfloor : stock < (⌊stock⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one stock
  have hsqrt : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hsquare : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX
  have hBreal : (B : ℝ) ≤ 16 * (⌊stock⌋₊ : ℝ) := by nlinarith
  have hB : B ≤ 16 * ⌊stock⌋₊ := by exact_mod_cast hBreal
  have hcast : ((16 * ⌊stock⌋₊ - B : ℕ) : ℝ) =
      16 * (⌊stock⌋₊ : ℝ) - B := by
    rw [Nat.cast_sub hB]
    push_cast
    rfl
  rw [hcast]
  nlinarith [sq_nonneg (16 * (⌊stock⌋₊ : ℝ) - B - 4 * Real.sqrt X)]

/-- The same reduction at FW's explicit real stock. It leaves the real
margin itself as an internal numerical obligation. -/
theorem fw_uniform_floored_stock_square_gate (X : ℝ) (B : ℕ)
    (hX : 0 ≤ X)
    (hmargin : (B : ℝ) + 16 + 4 * Real.sqrt X ≤ 16 * fwUniformRealStock X) :
    16 * X < (((16 * fwUniformNaturalStock X - B : ℕ) : ℝ) ^ 2) := by
  exact fw_floor_stock_square_gate X (fwUniformRealStock X) B hX hmargin

end
end Sude
