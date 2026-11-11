import Sude.UniformSqrtLog

/-! Elementary bounds on the square-root/log ratio used by the odd-prime
count repair. No prime-count or theta estimates are assumed. -/
namespace Sude
noncomputable section
open Real

/-- On the increasing branch, the square-root/log ratio is monotone. -/
theorem sqrt_log_ratio_mono_large {t X : ℝ} (ht : exp 2 ≤ t) (htX : t ≤ X) :
    sqrt t / log t ≤ sqrt X / log X := by
  have h2 : 1 < exp (2 : ℝ) := by simpa using exp_lt_exp.mpr (show (0 : ℝ) < 2 by norm_num)
  have ht1 : 1 < t := lt_of_lt_of_le h2 ht
  have hX1 : 1 < X := lt_of_lt_of_le ht1 htX
  have hlt : 0 < log t := log_pos ht1
  have hlX : 0 < log X := log_pos hX1
  have hsqt : 0 < sqrt t := sqrt_pos.2 (by linarith)
  have hsqX : 0 < sqrt X := sqrt_pos.2 (by linarith)
  have ha := Real.log_div_sqrt_antitoneOn ht (le_trans ht htX) htX
  have h' := (inv_le_inv₀ (div_pos hlt hsqt) (div_pos hlX hsqX)).2 ha
  simpa only [inv_div] using h'

/-- A uniform low-end bound, with the numerical exponential gate explicit. -/
theorem sqrt_log_ratio_low_bound {t : ℝ} (ht : 2 ≤ t) (ht8 : t ≤ exp 8)
    (hexp4 : exp 4 < 55) : sqrt t / log t < 55 / 8 := by
  have htpos : 0 < t := by linarith
  have hlog : 0 < log t := log_pos (by linarith)
  have hlog2 : (2 / 3 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hloglo : (2 / 3 : ℝ) < log t :=
    lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) ht)
  by_cases hbig : exp 2 ≤ t
  · have htX := sqrt_log_ratio_mono_large hbig ht8
    have hs : sqrt (exp 8) = exp 4 := by
      convert (Real.exp_half (8 : ℝ)).symm using 1 <;> norm_num
    rw [Real.log_exp, hs] at htX
    linarith
  · have he : exp (1 : ℝ) < 3 := by linarith [Real.exp_one_lt_d9]
    have hexp2 : exp (2 : ℝ) = exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    have hs : sqrt t < 3 := by
      have hepos := exp_pos (1 : ℝ)
      have hsqt := Real.sq_sqrt (le_of_lt htpos)
      have hsnon := Real.sqrt_nonneg t
      nlinarith
    apply (div_lt_iff₀ hlog).2
    nlinarith

/-- A lower endpoint comparison for the large-domain uniform bound. -/
theorem sqrt_log_ratio_lower_43_2 {X : ℝ} (hX : 0 < X)
    (hlog : (43 / 2 : ℝ) ≤ log X) (hgate : 45000 < exp (43 / 4 : ℝ)) :
    (90000 / 43 : ℝ) < sqrt X / log X := by
  have hExp : exp (43 / 2 : ℝ) ≤ X := by
    have h := Real.exp_le_exp.mpr hlog
    simpa [Real.exp_log hX] using h
  have hlo : exp 2 ≤ exp (43 / 2 : ℝ) := Real.exp_le_exp.mpr (by norm_num)
  have hmono := sqrt_log_ratio_mono_large hlo hExp
  have hs : sqrt (exp (43 / 2 : ℝ)) = exp (43 / 4 : ℝ) := by
    convert (Real.exp_half (43 / 2 : ℝ)).symm using 1 <;> norm_num
  rw [Real.log_exp, hs] at hmono
  have hbound : (90000 / 43 : ℝ) < exp (43 / 4 : ℝ) / (43 / 2 : ℝ) := by
    apply (lt_div_iff₀ (by norm_num)).2
    nlinarith
  exact hbound.trans_le hmono
end
end Sude
