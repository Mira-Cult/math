import Sude.OddPrimeLowJBound
import Sude.OddCountJHigh

/-! Combine the low- and high-range bounds for the Abel error kernel. -/

namespace Sude
noncomputable section
open Real MeasureTheory

/-- The kernel is interval-integrable on any bounded interval above 2. -/
theorem odd_j_kernel_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (sqrt t * log t ^ 2)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have htpos : 0 < t := by linarith [ht.1]
  have hs : sqrt t ≠ 0 := ne_of_gt (sqrt_pos.2 htpos)
  have hl : log t ≠ 0 := ne_of_gt (log_pos (by linarith [ht.1]))
  have hd : sqrt t * log t ^ 2 ≠ 0 := mul_ne_zero hs (pow_ne_zero 2 hl)
  exact ContinuousAt.continuousWithinAt (by fun_prop)

/-- The full integral from 2 has the stated bound on the high range,
including the endpoint x = exp 8. -/
theorem odd_count_j_global_high {x : ℝ} (hx : exp 8 ≤ x) :
    (∫ t in (2 : ℝ)..x, (sqrt t * log t ^ 2)⁻¹) <
      495 / 2 + 4 * (sqrt x / log x ^ 2) := by
  have hstart : (2 : ℝ) ≤ exp 8 := by
    have h := Real.add_one_le_exp (8 : ℝ)
    linarith
  have hlow := low_j_integral_lt_495_over_2 hstart (le_refl (exp 8))
  have hhigh := odd_count_j_high_integral hx
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (odd_j_kernel_integrable (a := 2) (b := exp 8) (by norm_num) hstart)
    (odd_j_kernel_integrable (a := exp 8) (b := x) hstart hx)
  simp only [one_div] at hhigh
  linarith
end
end Sude
