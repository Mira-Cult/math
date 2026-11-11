import Sude.FWActualPoolMean
import Sude.FWMeanLogLower
import Sude.FWLogUpper

/-! Discharge the logarithmic and BMOR cutoff premises of the actual FW
pool-mean bound using the explicit RS index hypotheses. -/
namespace Sude
noncomputable section

/-- The actual prescribed pool mean satisfies FW's interval throughout the
stated order range, conditional on the explicit published inputs. -/
theorem fw_actual_pool_mean_bounds_of_index (bmor : BMORFinitePiFour)
    (lower : RSIndexLower) (upper : RSIndexUpper) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤
      (Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ) ∧
    (Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ) ≤
      (123 / 250 : ℝ) * (poolMaximum n : ℝ) := by
  have hlo := (fw_poolMaximum_log_gt_181_eighths lower hnlo).le
  have hhi := (fw_poolMaximum_log_lt_29 upper hnlo hnhi).le
  have hnat := poolMaximum_below_two_pow_41 upper n (by omega) (by omega)
  have hcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ) := by
    have h : (poolMaximum n : ℝ) < (2 : ℝ)^41 := by exact_mod_cast hnat
    norm_num at h ⊢
    linarith
  exact fw_actual_pool_mean_bounds bmor lower hnlo hlo hhi hcap

end
end Sude
