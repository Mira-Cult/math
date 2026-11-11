import Sude.LiIntegralBridge
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open MeasureTheory Set
open scoped Interval
namespace Sude
noncomputable section

/-- Rectangular bounds for the positive, decreasing logarithmic kernel. -/
theorem li_kernel_interval_rational_bound {a b L U : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hL : 0 < L)
    (hlo : L ≤ Real.log a) (hhi : Real.log b ≤ U) :
    (b - a) / U ≤ (∫ t in a..b, (Real.log t)⁻¹) ∧
      (∫ t in a..b, (Real.log t)⁻¹) ≤ (b - a) / L := by
  have hlogb : 0 < Real.log b := Real.log_pos (by linarith)
  have hU : 0 < U := lt_of_lt_of_le hlogb hhi
  have hi := li_kernel_intervalIntegrable ha hab
  have hlo_integral : (∫ _t in a..b, U⁻¹) ≤ (∫ t in a..b, (Real.log t)⁻¹) := by
    apply intervalIntegral.integral_mono_on hab intervalIntegrable_const hi
    intro x hx
    have hxpos : 0 < x := by linarith [hx.1]
    have hxlog : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
    have hlog : Real.log x ≤ U := (Real.log_le_log hxpos hx.2).trans hhi
    exact (inv_le_inv₀ hU hxlog).2 hlog
  have hhi_integral : (∫ t in a..b, (Real.log t)⁻¹) ≤ (∫ _t in a..b, L⁻¹) := by
    apply intervalIntegral.integral_mono_on hab hi intervalIntegrable_const
    intro x hx
    have hloga : 0 < Real.log a := Real.log_pos ha
    have hlog : L ≤ Real.log x := hlo.trans (Real.log_le_log (by linarith) hx.1)
    exact (inv_le_inv₀ (lt_of_lt_of_le hL hlog) hL).2 hlog
  constructor
  · simpa [div_eq_mul_inv] using hlo_integral
  · simpa [div_eq_mul_inv] using hhi_integral

/-- Summed rectangular bounds for any finite monotone partition and any
supplied certified endpoint bounds. -/
theorem li_kernel_partition_rational_bound
    (p L U : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n)
    (ha : ∀ k ∈ Finset.Ico m n, 1 < p k)
    (horder : ∀ k ∈ Finset.Ico m n, p k ≤ p (k + 1))
    (hL : ∀ k ∈ Finset.Ico m n, 0 < L k)
    (hlo : ∀ k ∈ Finset.Ico m n, L k ≤ Real.log (p k))
    (hhi : ∀ k ∈ Finset.Ico m n, Real.log (p (k + 1)) ≤ U k) :
    (∑ k ∈ Finset.Ico m n, (p (k + 1) - p k) / U k) ≤
      (∫ t in p m..p n, (Real.log t)⁻¹) ∧
      (∫ t in p m..p n, (Real.log t)⁻¹) ≤
        (∑ k ∈ Finset.Ico m n, (p (k + 1) - p k) / L k) := by
  have hp : (∑ k ∈ Finset.Ico m n, ∫ t in p k..p (k + 1), (Real.log t)⁻¹) =
      ∫ t in p m..p n, (Real.log t)⁻¹ := by
    apply intervalIntegral.sum_integral_adjacent_intervals_Ico (a := p) hmn
    intro k hk
    have hk' : k ∈ Finset.Ico m n := by simpa only [Finset.mem_Ico, Set.mem_Ico] using hk
    exact li_kernel_intervalIntegrable (ha k hk') (horder k hk')
  rw [← hp]
  constructor <;> apply Finset.sum_le_sum <;> intro k hk
  · exact (li_kernel_interval_rational_bound (ha k hk) (horder k hk)
      (hL k hk) (hlo k hk) (hhi k hk)).1
  · exact (li_kernel_interval_rational_bound (ha k hk) (horder k hk)
      (hL k hk) (hlo k hk) (hhi k hk)).2

/-- Rational quadratic-order bounds for log(1+u) when u≥0. -/
theorem log_one_add_two_term_bounds {u : ℝ} (hu : 0 ≤ u) :
    let z := u / (u + 2)
    2 * (z + z ^ 3 / 3) ≤ Real.log (1 + u) ∧
      Real.log (1 + u) ≤ 2 * (z + z ^ 3 / 3 + z ^ 5 / (1 - z ^ 2)) := by
  dsimp only
  let z : ℝ := u / (u + 2)
  have hden : 0 < u + 2 := by linarith
  have hz0 : 0 ≤ z := div_nonneg hu (le_of_lt hden)
  have hz1 : z < 1 := (div_lt_one hden).2 (by linarith)
  have heq : (1 + z) / (1 - z) = 1 + u := by
    dsimp [z]
    field_simp
    ring
  have hl := Real.sum_range_le_log_div hz0 hz1 2
  have hh := Real.log_div_le_sum_range_add hz0 hz1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hl hh
  norm_num at hl hh
  rw [heq] at hl hh
  constructor <;> linarith

end
end Sude
