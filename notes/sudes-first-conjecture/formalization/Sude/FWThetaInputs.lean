import Sude.FWFirstBandAggregateEnvelopes
import Sude.OddCountUniformTheta

/-! FW mean, index and first-band numerical envelopes under the explicit
finite theta and RS hypotheses. The stronger classwise prime-count input
is not assumed or established. -/
namespace Sude
noncomputable section

/-- Existing FW index bounds put the actual pool maximum within the
finite theta-to-count domain. -/
theorem fw_pool_odd_count_uniform_of_theta (bmor : BMORFiniteTheta)
    (lower : RSIndexLower) (upper : RSIndexUpper) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    OddPrimeCountUniformBound (poolMaximum n : ℝ)
      ((1367 / 250 : ℝ) * (Real.sqrt (poolMaximum n : ℝ) /
        Real.log (poolMaximum n : ℝ))) := by
  have hlo := fw_poolMaximum_log_gt_181_eighths lower hnlo
  have hnat := poolMaximum_below_two_pow_41 upper n (by omega) (by omega)
  have hcap : (poolMaximum n : ℝ) ≤ (4 * 10 ^ 13 : ℝ) := by
    have h : (poolMaximum n : ℝ) < (2 : ℝ)^41 := by exact_mod_cast hnat
    norm_num at h ⊢
    linarith
  exact bmor_odd_count_uniform_bound_of_theta bmor (by linarith) hcap

/-- FW normalized mean from finite theta and RS index inputs. -/
theorem fw_actual_pool_normalized_mean_of_theta (bmor : BMORFiniteTheta)
    (lower : RSIndexLower) (upper : RSIndexUpper) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    (243 / 500 : ℝ) ≤ ((Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ)) /
      (poolMaximum n : ℝ) ∧
    ((Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ)) / (poolMaximum n : ℝ) ≤
      (123 / 250 : ℝ) := by
  exact fw_actual_pool_normalized_mean_of_aggregate lower hnlo
    (fw_poolMaximum_log_gt_181_eighths lower hnlo).le
    (fw_poolMaximum_log_lt_29 upper hnlo hnhi).le
    (fw_pool_odd_count_uniform_of_theta bmor lower upper hnlo hnhi)

/-- The unnormalized version for FW matched-bin supply. -/
theorem fw_actual_pool_mean_bounds_of_theta (bmor : BMORFiniteTheta)
    (lower : RSIndexLower) (upper : RSIndexUpper) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤
      (Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ) ∧
    (Lucas.poolTotal n : ℝ) / ((n*n : ℕ) : ℝ) ≤
      (123 / 250 : ℝ) * (poolMaximum n : ℝ) := by
  exact fw_actual_pool_mean_bounds_of_aggregate lower hnlo
    (fw_poolMaximum_log_gt_181_eighths lower hnlo).le
    (fw_poolMaximum_log_lt_29 upper hnlo hnhi).le
    (fw_pool_odd_count_uniform_of_theta bmor lower upper hnlo hnhi)

/-- FW3's index ratio from the same theta and RS inputs. -/
theorem fw_actual_index_ratio_of_theta (bmor : BMORFiniteTheta)
    (lower : RSIndexLower) (upper : RSIndexUpper) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    Real.log (poolMaximum n : ℝ) - 9/8 <
      (poolMaximum n : ℝ) / (n : ℝ)^2 := by
  exact fw_actual_index_ratio_of_aggregate lower upper hnlo hnhi
    (fw_pool_odd_count_uniform_of_theta bmor lower upper hnlo hnhi)

/-- First-band quota and stock envelopes with V equal to the actual log X.
This does not assert a growth trace or stage existence. -/
theorem fw_first_band_ww4_pointwise_envelopes_of_theta
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n j : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hj : j ≤ 238) :
    let X : ℝ := poolMaximum n
    let V : ℝ := Real.log X
    let m₀ : ℝ := 403 / 10000
    let qbar : ℝ := 1 / 69780
    let mf : ℝ := ((9999 / 10000 : ℝ) * (7525444 / 10000000)) / V
    let eps : ℝ := 23 / 48 - 3981035 / 10000000
    m₀ * X ≤ ((n * n : ℕ) : ℝ) - 13 - fwEarlyBudget n ∧
    ((6 * (n + 8) : ℕ) : ℝ) ≤ qbar * X ∧
    0 < mf ∧ mf ≤ m₀ - 2 * qbar * j ∧ 0 < eps ∧
    2 * eps * mf^2 ≥ 2 * 6 * qbar := by
  exact fw_first_band_ww4_pointwise_envelopes_of_aggregate lower upper upperSharp
    hnlo hnhi hj (fw_pool_odd_count_uniform_of_theta bmor lower upper hnlo (by omega))

end
end Sude
