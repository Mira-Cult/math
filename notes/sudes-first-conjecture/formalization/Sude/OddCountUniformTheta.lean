import Sude.OddPrimeThetaCountError
import Sude.OddPrimeLowJBound
import Sude.OddCountJGlobalHigh
import Sude.OddPrimeSqrtLogBounds
import Sude.OddCountExpGate
import Sude.OddCountUniformMean

/-! Theta-to-count uniform and pointwise estimates in the finite BMOR range. -/
namespace Sude
noncomputable section
open Real MeasureTheory
set_option maxHeartbeats 1600000

/-- Uniform odd-prime count estimate from the finite theta hypothesis.
The endpoint domain includes small t, while X has the stated logarithmic
lower bound. -/
theorem bmor_odd_count_uniform_of_theta (bmor : BMORFiniteTheta)
    {t X : ℝ} (ht : 2 ≤ t) (htX : t ≤ X)
    (hlog : (43 / 2 : ℝ) ≤ log X) (hcap : X ≤ (4 * 10 ^ 13 : ℝ)) :
    |oddPrimeCountReal t - liFromTwo t| <
      (1367 / 250 : ℝ) * (sqrt X / log X) := by
  have htpos : 0 < t := by linarith
  have hXpos : 0 < X := by linarith
  have hlX : 0 < log X := by linarith
  have hF := sqrt_log_ratio_lower_43_2 hXpos hlog odd_count_exp_43_fourths_gt_45000
  have hcount := bmor_odd_count_theta_integral_error bmor ht (le_trans htX hcap)
  have heq : (518 / 125 : ℝ) * sqrt t / log t =
      (518 / 125 : ℝ) * (sqrt t / log t) := by ring
  rw [heq] at hcount
  have hlog2 : (2 / 3 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hconst : (2 : ℝ) / log 2 < 3 := by
    apply (div_lt_iff₀ (by linarith : 0 < log 2)).2
    linarith
  have h4 : exp 4 < (55 : ℝ) := by
    have he : exp 1 < (68 / 25 : ℝ) := by linarith [Real.exp_one_lt_d9]
    have hp : (exp 1)^4 < ((68 / 25 : ℝ)^4) :=
      pow_lt_pow_left₀ he (by positivity) (by norm_num)
    rw [Real.exp_one_pow] at hp
    norm_num at hp ⊢
    linarith
  by_cases hsmall : t ≤ exp 8
  · have hf := sqrt_log_ratio_low_bound ht hsmall h4
    have hj := low_j_integral_lt_495_over_2 ht hsmall
    have htarget : (492120 / 43 : ℝ) < (1367 / 250 : ℝ) * (sqrt X / log X) := by
      nlinarith
    have herr : |oddPrimeCountReal t - liFromTwo t| < (105713 / 100 : ℝ) := by
      nlinarith
    linarith
  · have hbig : exp 8 ≤ t := le_of_not_ge hsmall
    have hExp : exp (2 : ℝ) ≤ exp 8 := Real.exp_le_exp.mpr (by norm_num)
    have hf := sqrt_log_ratio_mono_large (le_trans hExp hbig) htX
    have hg := odd_count_j_high_mono hbig (le_trans hbig htX) htX
    change sqrt t / log t ^ 2 ≤ sqrt X / log X ^ 2 at hg
    have hj := odd_count_j_global_high hbig
    have hratio : (4 : ℝ) / log X ≤ 8 / 43 := by
      apply (div_le_iff₀ hlX).2
      linarith
    have hFX : 0 ≤ sqrt X / log X := div_nonneg (sqrt_nonneg _) hlX.le
    have hgX : sqrt X / log X ^ 2 = (sqrt X / log X) / log X := by ring
    rw [hgX] at hg
    have hkg : 4 * (sqrt t / log t ^ 2) ≤ (8 / 43 : ℝ) * (sqrt X / log X) := by
      have hm := mul_le_mul_of_nonneg_right hratio hFX
      have heq : (4 / log X) * (sqrt X / log X) =
          4 * ((sqrt X / log X) / log X) := by ring
      rw [heq] at hm
      linarith
    have hlin : (25716 / 25 : ℝ) <
        (25716 / 25 : ℝ) * (43 / 90000) * (sqrt X / log X) := by
      nlinarith
    have hnum : (518 / 125 : ℝ) * (1 + 8 / 43) +
        (25716 / 25 : ℝ) * (43 / 90000) < 1367 / 250 := by norm_num
    nlinarith

/-- The uniform estimate supplies the generic pool-mean count interface;
it does not assert the stronger classwise `BMORFinitePiFour` proposition. -/
theorem bmor_odd_count_uniform_bound_of_theta (bmor : BMORFiniteTheta)
    {X : ℝ} (hlog : (43 / 2 : ℝ) ≤ log X)
    (hcap : X ≤ (4 * 10 ^ 13 : ℝ)) :
    OddPrimeCountUniformBound X ((1367 / 250 : ℝ) * (sqrt X / log X)) := by
  intro t ht htX
  exact le_of_lt (bmor_odd_count_uniform_of_theta bmor ht htX hlog hcap)

/-- Taking the uniform endpoint as t gives the large-endpoint pointwise
estimate; no pointwise claim is made below its logarithmic threshold. -/
theorem bmor_odd_count_pointwise_of_theta (bmor : BMORFiniteTheta)
    {t : ℝ} (ht : 2 ≤ t) (hlog : (43 / 2 : ℝ) ≤ log t)
    (hcap : t ≤ (4 * 10 ^ 13 : ℝ)) :
    |oddPrimeCountReal t - liFromTwo t| <
      (1367 / 250 : ℝ) * (sqrt t / log t) :=
  bmor_odd_count_uniform_of_theta bmor ht le_rfl hlog hcap
end
end Sude
