import Sude.LiBGPropagation

/-! Exact exponential estimates for absorbing coarse Li comparison errors.
These are elementary inequalities and assume no Li estimate. -/
namespace Sude

/-- The lower-comparison derivative gain exceeds 82 when u ≥ 22. -/
theorem bg_lower_exp_dominance {u : ℝ} (hu : 22 ≤ u) :
    82 < 12 * Real.exp u / u ^ 5 := by
  have hup : 0 < u := by linarith
  have ht := Real.pow_div_factorial_le_exp u (le_of_lt hup) 13
  have hpow : (22 : ℝ)^8 ≤ u^8 := pow_le_pow_left₀ (by norm_num) hu _
  have hmul := mul_le_mul_of_nonneg_right hpow (show 0 ≤ u^5 by positivity)
  have hpos : 0 < u^5 := by positivity
  have hnum : (82 : ℝ) * 6227020800 < 12 * 22^8 := by norm_num
  have hfactor : (Nat.factorial 13 : ℝ) = 6227020800 := by norm_num
  rw [hfactor] at ht
  have hterm : 82 * u^5 < 12 * (u^13 / 6227020800) := by
    have hpowid : u^13 = u^8 * u^5 := by ring
    rw [hpowid]
    have hgap : 0 < (12 * 22^8 - 82 * 6227020800) * u^5 :=
      mul_pos (by linarith) hpos
    have : 12 * (22 : ℝ)^8 * u^5 ≤ 12 * (u^8 * u^5) := by nlinarith
    have : 82 * u^5 * 6227020800 < 12 * (u^8 * u^5) := by nlinarith
    linarith
  apply (lt_div_iff₀ hpos).2
  nlinarith

/-- The upper-comparison derivative gain exceeds 1458 when u ≥ 22. -/
theorem bg_upper_exp_dominance {u : ℝ} (hu : 22 ≤ u) :
    1458 < Real.exp u / (2 * u ^ 3) := by
  have hup : 0 < u := by linarith
  have ht := Real.pow_div_factorial_le_exp u (le_of_lt hup) 13
  have hpow : (22 : ℝ)^10 ≤ u^10 := pow_le_pow_left₀ (by norm_num) hu _
  have hmul := mul_le_mul_of_nonneg_right hpow (show 0 ≤ u^3 by positivity)
  have hpos : 0 < u^3 := by positivity
  have hnum : (2916 : ℝ) * 6227020800 < 22^10 := by norm_num
  have hfactor : (Nat.factorial 13 : ℝ) = 6227020800 := by norm_num
  rw [hfactor] at ht
  have hterm : 2916 * u^3 < u^13 / 6227020800 := by
    have hpowid : u^13 = u^10 * u^3 := by ring
    rw [hpowid]
    have hgap : 0 < (22^10 - 2916 * 6227020800) * u^3 :=
      mul_pos (by linarith) hpos
    have : 2916 * u^3 * 6227020800 < u^10 * u^3 := by nlinarith
    linarith
  apply (lt_div_iff₀ (by positivity : 0 < 2 * u^3)).2
  linarith

end Sude
