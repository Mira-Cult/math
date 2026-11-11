import Sude.LiIntegralBridge
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Low-range bound for the square-root logarithmic Abel error kernel. -/

open Real MeasureTheory
namespace Sude
noncomputable section
set_option maxHeartbeats 800000

/-- The logarithmic factor is bounded by its value at 2, and the remaining
square-root kernel integrates exactly. -/
theorem low_sqrt_log_integral_bound {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, (sqrt t * log t ^ 2)⁻¹) ≤
      (9 / 2 : ℝ) * (sqrt x - sqrt 2) := by
  have hcont : ContinuousOn (fun t : ℝ => (sqrt t * log t ^ 2)⁻¹) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx]
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have ht0n : t ≠ 0 := ne_of_gt ht0
    have hs : sqrt t ≠ 0 := ne_of_gt (sqrt_pos.2 ht0)
    have hl : log t ≠ 0 := ne_of_gt (log_pos (by linarith [ht.1]))
    have hd : sqrt t * log t ^ 2 ≠ 0 := mul_ne_zero hs (pow_ne_zero 2 hl)
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hcont2 : ContinuousOn (fun t : ℝ => (sqrt t)⁻¹) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx]
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hs : sqrt t ≠ 0 := ne_of_gt (sqrt_pos.2 ht0)
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hd : ∀ t ∈ Set.uIcc 2 x, HasDerivAt (fun u : ℝ => 2 * sqrt u) (sqrt t)⁻¹ t := by
    rw [Set.uIcc_of_le hx]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hs : sqrt t ≠ 0 := ne_of_gt (sqrt_pos.2 (by linarith [ht.1]))
    have h := (Real.hasDerivAt_sqrt ht0).const_mul 2
    have he : (2 : ℝ) * (1 / (2 * sqrt t)) = (sqrt t)⁻¹ := by field_simp
    rw [he] at h
    exact h
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont2.intervalIntegrable
  have hlog2 : (2 / 3 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
  have hmono : (∫ t in (2 : ℝ)..x, (sqrt t * log t ^ 2)⁻¹) ≤
      ∫ t in (2 : ℝ)..x, (9 / 4 : ℝ) * (sqrt t)⁻¹ := by
    apply intervalIntegral.integral_mono_on hx hcont.intervalIntegrable (hcont2.const_mul _).intervalIntegrable
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have hs : 0 ≤ (sqrt t)⁻¹ := inv_nonneg.mpr (sqrt_nonneg _)
    have hlog : (2 / 3 : ℝ) ≤ log t := hlog2.trans (log_le_log (by norm_num) ht.1)
    have hsq : (4 / 9 : ℝ) ≤ log t ^ 2 := by nlinarith
    have hinv : (log t ^ 2)⁻¹ ≤ (9 / 4 : ℝ) := by
      have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4 / 9) hsq
      norm_num at hh ⊢
      exact hh
    rw [mul_inv_rev]
    nlinarith
  rw [intervalIntegral.integral_const_mul, hi] at hmono
  linarith


/-- The low-range estimate used in the theta-only prime-count repair. -/
theorem low_j_integral_lt_495_over_2 {x : ℝ} (hx : 2 ≤ x) (hmax : x ≤ exp 8) :
    (∫ t in (2 : ℝ)..x, (sqrt t * log t ^ 2)⁻¹) < 495 / 2 := by
  have hex : exp 4 < (55 : ℝ) := by
    have he : exp 1 < (68/25 : ℝ) := by linarith [Real.exp_one_lt_d9]
    have hp : (exp 1)^4 < ((68/25 : ℝ)^4) :=
      pow_lt_pow_left₀ he (by positivity) (by norm_num)
    rw [Real.exp_one_pow] at hp
    norm_num at hp ⊢
    linarith
  have hexsq : exp 8 = exp 4 * exp 4 := by
    rw [← Real.exp_add]
    norm_num
  have hs8 : sqrt (exp 8) = exp 4 := by
    have hp : 0 < exp (4 : ℝ) := exp_pos _
    have he : 0 ≤ exp (8 : ℝ) := (exp_pos _).le
    have hs : sqrt (exp 8) ^ 2 = exp 4 * exp 4 := by
      rw [sq_sqrt he, hexsq]
    nlinarith [sqrt_nonneg (exp 8)]
  have hs : sqrt x ≤ exp 4 := by
    rw [← hs8]
    exact sqrt_le_sqrt hmax
  have h := low_sqrt_log_integral_bound hx
  have hs2 : 0 ≤ sqrt (2 : ℝ) := sqrt_nonneg _
  nlinarith

end
end Sude
