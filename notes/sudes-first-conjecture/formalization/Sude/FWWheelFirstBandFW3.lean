import Sude.FWWheelActualStock

/-! Conditional first-band WW4 quota from the explicit FW3 source bounds.
See `problems/prime-line-sums/manuscripts/cutoff2_controller_far_wide.md`
FW3 and FW13. The FW3 prime-count inequalities are hypotheses here, not
consequences of the existing sharp prime-index estimate. -/
namespace Sude
noncomputable section

/-- The two explicitly supplied FW3 inequalities imply the sharp index ratio
needed for the conditional first-band quota. -/
theorem fw_poolMaximum_index_ratio_of_fw3 {n : ℕ} (hn : 0 < n)
    (hlog : (181 / 8 : ℝ) < Real.log (poolMaximum n : ℝ))
    (hratio : Real.log (poolMaximum n : ℝ) - 9 / 8 <
      (poolMaximum n : ℝ) / (n : ℝ)^2) :
    (43 / 2 : ℝ) * (n : ℝ)^2 < poolMaximum n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < (n : ℝ)^2 := pow_pos hnpos _
  have hdiv : (43 / 2 : ℝ) < (poolMaximum n : ℝ) / (n : ℝ)^2 := by linarith
  exact (lt_div_iff₀ hsq).mp hdiv

/-- In the first-band conditional envelope, the literal FW3 prime-count
hypotheses discharge the index-ratio input of the WW4 quota theorem. The
supplied V envelope remains explicit; the rate here is the actual Q/X. -/
theorem fw_wheel_ww4_first_band_quota_of_fw3 {n : ℕ} {V : ℝ}
    (hn : 19485 ≤ n)
    (hlog : (181 / 8 : ℝ) < Real.log (poolMaximum n : ℝ))
    (hratio : Real.log (poolMaximum n : ℝ) - 9 / 8 <
      (poolMaximum n : ℝ) / (n : ℝ)^2)
    (hVpos : 0 < V) (hV : V ≤ 231 / 10) :
    2 * (23 / 48 - 3981035 / 10000000 : ℝ) *
      (((9999 / 10000 : ℝ) * (7525444 / 10000000)) / V)^2 ≥
    2 * 6 * (((6 * (n + 8) : ℕ) : ℝ) / poolMaximum n) := by
  have hX := fw_poolMaximum_index_ratio_of_fw3 (show 0 < n by omega) hlog hratio
  exact fw_wheel_ww4_first_band_quota (show 19483 ≤ n by omega) (le_of_lt hX) hVpos hV

end
end Sude
