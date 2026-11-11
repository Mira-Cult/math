import Sude.LiBGCoarseBase
import Mathlib.Analysis.Complex.ExponentialBounds

/-! A rational lower gate used by the theta-only odd-count repair. -/

namespace Sude

/-- Exact gate for the square-root scale at `log X ≥ 43/2`. -/
theorem odd_count_exp_43_fourths_gt_45000 : (45000 : ℝ) < Real.exp (43 / 4) := by
  have he : (1359 / 500 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hf : (43 / 40 : ℝ) ≤ Real.exp (3 / 40) := by
    have h := Real.add_one_le_exp (3 / 40 : ℝ)
    linarith
  have hp : (1359 / 500 : ℝ) * (43 / 40) < Real.exp (43 / 40) := by
    have hmul := mul_lt_mul_of_pos_right he (show (0 : ℝ) < 43 / 40 by norm_num)
    have hm := mul_le_mul_of_nonneg_left hf (le_of_lt (Real.exp_pos 1))
    have hsum : (1 : ℝ) + 3 / 40 = 43 / 40 := by norm_num
    rw [← Real.exp_add, hsum] at hm
    exact hmul.trans_le hm
  have hpow : ((1359 / 500 : ℝ) * (43 / 40)) ^ 10 < (Real.exp (43 / 40)) ^ 10 :=
    pow_lt_pow_left₀ hp (by norm_num) (by norm_num)
  rw [← Real.exp_nat_mul] at hpow
  norm_num at hpow ⊢
  linarith

end Sude
