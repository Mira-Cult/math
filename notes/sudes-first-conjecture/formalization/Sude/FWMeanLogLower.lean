import Sude.PrimeIndex

/-! Derive the FW lower logarithmic endpoint from the existing RS index
hypothesis and the explicit minimum order. No new source input is used. -/
namespace Sude
noncomputable section

/-- In the FW order range, the prescribed maximum lies above the left
endpoint of the finite mean-domain partition. -/
theorem fw_poolMaximum_log_gt_181_eighths (lower : RSIndexLower) {n : ℕ}
    (hn : 19485 ≤ n) :
    (181 / 8 : ℝ) < Real.log (poolMaximum n : ℝ) := by
  have hnreal : (19485 : ℝ) ≤ n := by exact_mod_cast hn
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hj : (379665226 : ℝ) ≤ j := by
    dsimp [j]
    push_cast
    nlinarith
  have hjpos : 0 < j := by linarith
  have hj2 : (2 : ℝ)^57 < j^2 := by
    norm_num
    nlinarith
  have hlogj : (79 / 4 : ℝ) < Real.log j := by
    have h := Real.log_lt_log (show (0 : ℝ) < (2 : ℝ)^57 by positivity) hj2
    rw [Real.log_pow, Real.log_pow] at h
    have hlog2 := Real.log_two_gt_d9
    norm_num at h hlog2 ⊢
    linarith
  have hsource : j * Real.log j < (poolMaximum n : ℝ) := by
    simpa [j] using poolMaximum_lower lower n
  have hscaled : j * (79 / 4 : ℝ) < j * Real.log j :=
    mul_lt_mul_of_pos_left hlogj hjpos
  have hX : (109 : ℝ) * 2^26 < (poolMaximum n : ℝ) := by
    have hval : (109 : ℝ) * 2^26 < (379665226 : ℝ) * (79 / 4) := by norm_num
    nlinarith
  have hpow : (2 : ℝ)^262 < (poolMaximum n : ℝ)^8 := by
    have hconstants : (2 : ℝ)^262 < ((109 : ℝ) * 2^26)^8 := by
      have hid : (2 : ℝ)^262 = ((2 : ℝ)^131)^2 := by
        rw [← pow_mul]
      rw [hid]
      norm_num
    exact hconstants.trans (pow_lt_pow_left₀ hX (by positivity) (by norm_num))
  have hlog := Real.log_lt_log (show (0 : ℝ) < (2 : ℝ)^262 by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  have hlog2 := Real.log_two_gt_d9
  norm_num at hlog hlog2 ⊢
  linarith

end
end Sude
