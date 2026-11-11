import Sude.FWFiniteGates
import Mathlib.Tactic.Ring

/-! Exact first-band arithmetic for the growth midpoint component only.
This does not imply a complete-line or FW18 bound. -/
namespace Sude
noncomputable section

/-- The integer binary allocation depth is exactly 17 on the first FW band. -/
theorem fw_growth_first_band_depth (n : ℕ) (hlo : 19485 ≤ n) (hhi : n ≤ 21248) :
    Nat.clog 2 (6 * n) = 17 := by
  have hu : Nat.clog 2 (6*n) ≤ 17 := by
    apply Nat.clog_le_of_le_pow
    norm_num
    omega
  have hl : 16 < Nat.clog 2 (6*n) := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).2
    norm_num
    omega
  omega

/-- The row/column growth midpoint invoice has this exact first-band
expression. This scalar identity assumes no statement about the square. -/
theorem fw_growth_first_band_midpoint_expression (n : ℕ) (hlo : 19485 ≤ n)
    (hhi : n ≤ 21248) (X : ℝ) :
    (Nat.clog 2 (6*n) : ℝ) * (8*(X/6)) + 3*(X/6)/(n : ℝ) + 2*(X/6) =
      23*X + X/(2*(n : ℝ)) := by
  rw [fw_growth_first_band_depth n hlo hhi]
  push_cast
  ring

/-- For nonnegative X, the pointwise first-band growth midpoint invoice is
at most `(896311/38970)*X`. It is a single component, not a full-line bound. -/
theorem fw_growth_first_band_midpoint_gate (n : ℕ) (hlo : 19485 ≤ n)
    (hhi : n ≤ 21248) (X : ℝ) (hX : 0 ≤ X) :
    (Nat.clog 2 (6*n) : ℝ) * (8*(X/6)) + 3*(X/6)/(n : ℝ) + 2*(X/6) ≤
      (896311/38970 : ℝ) * X := by
  rw [fw_growth_first_band_midpoint_expression n hlo hhi X]
  have hn : (19485 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlo
  have hp : (0 : ℝ) < 2*(n : ℝ) := by linarith
  have hi : (1 : ℝ)/(2*(n : ℝ)) ≤ 1/38970 := by
    apply (div_le_div_iff₀ hp (by norm_num : (0 : ℝ) < 38970)).2
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hi hX
  have hh : X * (1/(2*(n : ℝ))) = X/(2*(n : ℝ)) := by ring
  rw [hh] at hmul
  nlinarith

end
end Sude
