import Sude.PrimeIndex

/-! FW3's logarithmic upper domain from the declared RS upper estimate. -/
namespace Sude
noncomputable section

/-- Every order in the FW domain has `ln X < 29`, with the natural
logarithm and a kernel-checked rational upper bound for `ln 2`. -/
theorem fw_poolMaximum_log_lt_29 (upper : RSIndexUpper) {n : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    Real.log (poolMaximum n : ℝ) < 29 := by
  have hnat : poolMaximum n < 2 ^ 41 :=
    poolMaximum_below_two_pow_41 upper n (by omega) (by omega)
  have hpos : (0 : ℝ) < poolMaximum n := by
    exact_mod_cast (poolMaximum_prime n).pos
  have hbound : (poolMaximum n : ℝ) ≤ (2 : ℝ) ^ 41 := by
    exact_mod_cast le_of_lt hnat
  have h := Real.log_le_log hpos hbound
  rw [Real.log_pow] at h
  have hlog2 : Real.log 2 < (7 : ℝ) / 10 := by linarith [Real.log_two_lt_d9]
  norm_num at h
  linarith

end
end Sude
