import Sude.OddPrimeAbelIntegral
import Sude.OddPrimeAbelMainTerm

/-! Exact residual identity and a conditional theta-to-count error bound. -/

namespace Sude
noncomputable section
open Finset Real MeasureTheory
set_option maxHeartbeats 800000

/-- The odd-prime theta kernel is integrable on every finite interval
starting at 2, including intervals with no odd primes. -/
theorem odd_theta_integrableOn (x : ℝ) :
    IntegrableOn (fun t ↦ thetaAP t 2 1 / (t * log t ^ 2)) (Set.Icc 2 x) volume := by
  let a : ℕ → ℝ := fun n ↦ if Nat.Prime n ∧ (n : ℤ) % 2 = 1 then log n else 0
  have heq (t : ℝ) : thetaAP t 2 1 = ∑ n ∈ Icc 0 ⌊t⌋₊, a n := by
    simp [thetaAP, a, _root_.Nat.range_succ_eq_Icc_zero]
  conv => arg 1; ext t; rw [heq, div_eq_mul_one_div, mul_comm]
  refine integrableOn_mul_sum_Icc _ (by norm_num) <| ContinuousOn.integrableOn_Icc fun t ht ↦
    ContinuousAt.continuousWithinAt ?_
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hl : log t ≠ 0 := ne_of_gt (log_pos (by linarith [ht.1]))
  have hl2 : log t ^ 2 ≠ 0 := pow_ne_zero 2 hl
  have hden : t * log t ^ 2 ≠ 0 := mul_ne_zero ht0 hl2
  fun_prop

/-- Subtracting the exact Abel main term leaves the theta error and the
explicit lower-endpoint contribution. -/
theorem odd_count_theta_error_identity {x : ℝ} (hx : 2 ≤ x) :
    oddPrimeCountReal x - liFromTwo x =
      (thetaAP x 2 1 - x) / log x +
      (∫ t in (2 : ℝ)..x, (thetaAP t 2 1 - t) / (t * log t ^ 2)) + 2 / log 2 := by
  have hiθ : IntervalIntegrable (fun t ↦ thetaAP t 2 1 / (t * log t ^ 2)) volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr (odd_theta_integrableOn x)
  have hi1 : IntervalIntegrable (fun t : ℝ => (log t ^ 2)⁻¹) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := ne_of_gt (log_pos (by linarith [ht.1]))
    have hl2 : log t ^ 2 ≠ 0 := pow_ne_zero 2 hl
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hI : (∫ t in (2 : ℝ)..x, (thetaAP t 2 1 - t) / (t * log t ^ 2)) =
      (∫ t in (2 : ℝ)..x, thetaAP t 2 1 / (t * log t ^ 2)) -
      (∫ t in (2 : ℝ)..x, (log t ^ 2)⁻¹) := by
    calc
      _ = ∫ t in (2 : ℝ)..x, (thetaAP t 2 1 / (t * log t ^ 2) - (log t ^ 2)⁻¹) := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le hx]
        intro t ht
        have ht0 : t ≠ 0 := by linarith [ht.1]
        have hl : log t ≠ 0 := ne_of_gt (log_pos (by linarith [ht.1]))
        field_simp
      _ = _ := intervalIntegral.integral_sub hiθ hi1
  have ha := oddPrimeCountReal_eq_theta_div_log_add_integral hx
  have hm := odd_li_mainterm hx
  rw [hI, sub_div]
  linarith

/-- A supplied theta error bounds the count error by an explicit integral. -/
theorem odd_count_theta_error_bound {x C : ℝ} (hx : 2 ≤ x)
    (hθ : ∀ t ∈ Set.Icc 2 x, |thetaAP t 2 1 - t| ≤ C * sqrt t) :
    |oddPrimeCountReal x - liFromTwo x| ≤
      C * sqrt x / log x +
      (∫ t in (2 : ℝ)..x, C * sqrt t / (t * log t ^ 2)) + 2 / log 2 := by
  have hiθ : IntervalIntegrable (fun t ↦ thetaAP t 2 1 / (t * log t ^ 2)) volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr (odd_theta_integrableOn x)
  have hi1 : IntervalIntegrable (fun t : ℝ => (log t ^ 2)⁻¹) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := ne_of_gt (log_pos (by linarith [ht.1]))
    have hl2 : log t ^ 2 ≠ 0 := pow_ne_zero 2 hl
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hres : IntervalIntegrable (fun t : ℝ => (thetaAP t 2 1 - t) / (t * log t ^ 2)) volume 2 x := by
    apply IntervalIntegrable.congr _ (hiθ.sub hi1)
    rw [Set.uIoc_of_le hx]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := ne_of_gt (log_pos (by linarith [ht.1]))
    field_simp
  have hbound : IntervalIntegrable (fun t : ℝ => C * sqrt t / (t * log t ^ 2)) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := ne_of_gt (log_pos (by linarith [ht.1]))
    have hl2 : log t ^ 2 ≠ 0 := pow_ne_zero 2 hl
    have hden : t * log t ^ 2 ≠ 0 := mul_ne_zero ht0 hl2
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hlx : 0 < log x := log_pos (by linarith)
  have habs0 : 0 ≤ 2 / log 2 := by positivity
  have hfirst : |(thetaAP x 2 1 - x) / log x| ≤ C * sqrt x / log x := by
    rw [abs_div, abs_of_pos hlx]
    exact div_le_div_of_nonneg_right (hθ x ⟨hx, le_rfl⟩) hlx.le
  have hI : |∫ t in (2 : ℝ)..x, (thetaAP t 2 1 - t) / (t * log t ^ 2)| ≤
      ∫ t in (2 : ℝ)..x, C * sqrt t / (t * log t ^ 2) := by
    calc
      _ ≤ ∫ t in (2 : ℝ)..x, |(thetaAP t 2 1 - t) / (t * log t ^ 2)| :=
        intervalIntegral.abs_integral_le_integral_abs hx
      _ ≤ _ := by
        apply intervalIntegral.integral_mono_on hx hres.abs hbound
        intro t ht
        have htpos : 0 < t := by linarith [ht.1]
        have hl : 0 < log t := log_pos (by linarith [ht.1])
        have hden : 0 < t * log t ^ 2 := mul_pos htpos (sq_pos_of_pos hl)
        rw [abs_div, abs_of_pos hden]
        exact div_le_div_of_nonneg_right (hθ t ht) hden.le
  rw [odd_count_theta_error_identity hx]
  calc
    _ ≤ |(thetaAP x 2 1 - x) / log x| +
      |∫ t in (2 : ℝ)..x, (thetaAP t 2 1 - t) / (t * log t ^ 2)| + |2 / log 2| := by
      calc
        _ ≤ |(thetaAP x 2 1 - x) / log x +
            (∫ t in (2 : ℝ)..x, (thetaAP t 2 1 - t) / (t * log t ^ 2))| +
            |2 / log 2| := abs_add_le _ _
        _ ≤ _ := by gcongr; exact abs_add_le _ _
    _ ≤ _ := by rw [abs_of_nonneg habs0]; linarith



/-- A pointwise theta error implies the corresponding odd-prime count
error, with the integrable square-root kernel left explicit. -/
theorem odd_count_theta_error_sqrt {x C : ℝ} (hx : 2 ≤ x)
    (hθ : ∀ t ∈ Set.Icc 2 x, |thetaAP t 2 1 - t| ≤ C * sqrt t) :
    |oddPrimeCountReal x - liFromTwo x| ≤
      C * sqrt x / log x +
      C * (∫ t in (2 : ℝ)..x, (sqrt t * log t ^ 2)⁻¹) + 2 / log 2 := by
  have h := odd_count_theta_error_bound hx hθ
  have heq : (∫ t in (2 : ℝ)..x, C * sqrt t / (t * log t ^ 2)) =
      C * (∫ t in (2 : ℝ)..x, (sqrt t * log t ^ 2)⁻¹) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hx]
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have hspos : 0 < sqrt t := sqrt_pos.2 htpos
    have hl : 0 < log t := log_pos (by linarith [ht.1])
    have ht_eq : sqrt t ^ 2 = t := sq_sqrt htpos.le
    field_simp
    rw [ht_eq]
  rwa [heq] at h

/-- The exact Abel error bound under the existing finite BMOR theta
input; the remaining integral is not estimated in this theorem. -/
theorem bmor_odd_count_theta_integral_error (bmor : BMORFiniteTheta)
    {x : ℝ} (hx : 2 ≤ x) (hcap : x ≤ (4 * 10 ^ 13 : ℝ)) :
    |oddPrimeCountReal x - liFromTwo x| ≤
      (518 / 125 : ℝ) * sqrt x / log x +
      (518 / 125 : ℝ) * (∫ t in (2 : ℝ)..x, (sqrt t * log t ^ 2)⁻¹) +
      2 / log 2 := by
  apply odd_count_theta_error_sqrt hx
  intro t ht
  exact bmor_theta_two_via_four bmor t (by linarith [ht.1]) (le_trans ht.2 hcap)

end
end Sude
