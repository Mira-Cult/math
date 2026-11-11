import Sude.LiIntegralBridge
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! A high-range integral estimate used in the conditional theta-to-count route. -/
namespace Sude
noncomputable section
open Real MeasureTheory

/-- Derivative of the auxiliary function sqrt(t)/log(t)^2. -/
theorem odd_count_j_high_derivative {t : ℝ} (ht : 0 < t) (hl : log t ≠ 0) :
    HasDerivAt (fun y : ℝ => sqrt y / log y ^ 2)
      ((log t - 4) / (2 * sqrt t * log t ^ 3)) t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hs : sqrt t ≠ 0 := ne_of_gt (sqrt_pos.mpr ht)
  have hl2 : log t ^ 2 ≠ 0 := pow_ne_zero 2 hl
  have h := (Real.hasDerivAt_sqrt ht0).div ((Real.hasDerivAt_log ht0).pow 2) hl2
  convert h using 1 <;> try rfl
  simp only [Pi.pow_apply]
  have hsq : sqrt t ^ 2 = t := sq_sqrt ht.le
  field_simp
  norm_num
  rw [hsq]
  ring

/-- On log(t) ≥ 8, four times the auxiliary derivative pays the J integrand. -/
theorem odd_count_j_integrand_le_four_derivative {t : ℝ}
    (ht : 0 < t) (hlog : 8 ≤ log t) :
    1 / (sqrt t * log t ^ 2) ≤
      4 * ((log t - 4) / (2 * sqrt t * log t ^ 3)) := by
  have hlogpos : 0 < log t := by linarith
  have hsqrt : 0 < sqrt t := sqrt_pos.mpr ht
  have hd : 0 ≤ sqrt t * log t ^ 2 := by positivity
  have hratio : (1 : ℝ) ≤ 4 * (1 / 2 - 2 / log t) := by
    have h : (8 : ℝ) / log t ≤ 1 := (div_le_one hlogpos).2 hlog
    have heq : 4 * (1 / 2 - 2 / log t) = 2 - 8 / log t := by ring
    rw [heq]
    linarith
  calc
    _ ≤ (4 * (1 / 2 - 2 / log t)) / (sqrt t * log t ^ 2) :=
      div_le_div_of_nonneg_right hratio hd
    _ = _ := by field_simp; ring

/-- High part of J, including the endpoint x=exp 8. -/
theorem odd_count_j_high_integral {x : ℝ} (hx : exp 8 ≤ x) :
    (∫ t in exp 8..x, 1 / (sqrt t * log t ^ 2)) ≤
      4 * (sqrt x / log x ^ 2) := by
  let d : ℝ → ℝ := fun t => 4 * ((log t - 4) / (2 * sqrt t * log t ^ 3))
  have hstart : 0 < exp 8 := exp_pos _
  have htdata (t : ℝ) (ht : t ∈ Set.Icc (exp 8) x) : 0 < t ∧ 8 ≤ log t := by
    have hp : 0 < t := lt_of_lt_of_le hstart ht.1
    have hl : log (exp 8) ≤ log t := log_le_log hstart ht.1
    exact ⟨hp, by simpa using hl⟩
  have hg : IntervalIntegrable (fun t : ℝ => 1 / (sqrt t * log t ^ 2)) volume (exp 8) x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    intro t ht
    obtain ⟨hp, hl⟩ := htdata t ht
    have ht0 : t ≠ 0 := ne_of_gt hp
    have hs : sqrt t ≠ 0 := ne_of_gt (sqrt_pos.mpr hp)
    have hlog : log t ≠ 0 := by linarith
    have hden : sqrt t * log t ^ 2 ≠ 0 := mul_ne_zero hs (pow_ne_zero _ hlog)
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hd : IntervalIntegrable d volume (exp 8) x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    intro t ht
    obtain ⟨hp, hl⟩ := htdata t ht
    have ht0 : t ≠ 0 := ne_of_gt hp
    have hs : sqrt t ≠ 0 := ne_of_gt (sqrt_pos.mpr hp)
    have hlog : log t ≠ 0 := by linarith
    have hden : 2 * sqrt t * log t ^ 3 ≠ 0 := by positivity
    dsimp [d]
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hderiv : ∀ t ∈ Set.uIcc (exp 8) x,
      HasDerivAt (fun y : ℝ => 4 * (sqrt y / log y ^ 2)) (d t) t := by
    rw [Set.uIcc_of_le hx]
    intro t ht
    obtain ⟨hp, hl⟩ := htdata t ht
    have hlog : log t ≠ 0 := by linarith
    simpa [d] using (odd_count_j_high_derivative hp hlog).const_mul 4
  have heval := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hd
  have hcompare : (∫ t in exp 8..x, 1 / (sqrt t * log t ^ 2)) ≤
      ∫ t in exp 8..x, d t := by
    apply intervalIntegral.integral_mono_on hx hg hd
    intro t ht
    obtain ⟨hp, hl⟩ := htdata t ht
    exact odd_count_j_integrand_le_four_derivative hp hl
  have hbase : 0 ≤ 4 * (sqrt (exp 8) / log (exp 8) ^ 2) := by positivity
  rw [heval] at hcompare
  linarith

/-- The auxiliary function is nondecreasing on the high range. -/
theorem odd_count_j_high_mono :
    MonotoneOn (fun t : ℝ => sqrt t / log t ^ 2) (Set.Ici (exp 8)) := by
  have hdata (t : ℝ) (ht : exp 8 ≤ t) : 0 < t ∧ 8 ≤ log t := by
    have hp : 0 < t := lt_of_lt_of_le (exp_pos _) ht
    have hl : log (exp 8) ≤ log t := log_le_log (exp_pos _) ht
    exact ⟨hp, by simpa using hl⟩
  apply monotoneOn_of_deriv_nonneg (convex_Ici (exp 8))
  · intro t ht
    obtain ⟨hp, hl⟩ := hdata t ht
    have hlog : log t ≠ 0 := by linarith
    exact (odd_count_j_high_derivative hp hlog).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : exp 8 ≤ t := le_of_lt (by simpa using ht)
    obtain ⟨hp, hl⟩ := hdata t ht'
    have hlog : log t ≠ 0 := by linarith
    exact (odd_count_j_high_derivative hp hlog).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : exp 8 ≤ t := le_of_lt (by simpa using ht)
    obtain ⟨hp, hl⟩ := hdata t ht'
    have hlog : log t ≠ 0 := by linarith
    rw [(odd_count_j_high_derivative hp hlog).deriv]
    apply div_nonneg
    · linarith
    · positivity

end
end Sude
