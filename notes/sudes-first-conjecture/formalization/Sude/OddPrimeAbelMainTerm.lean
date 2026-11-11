import Sude.LiIntegralBridge
import Mathlib.NumberTheory.Chebyshev

/-! The elementary main term for the odd-prime Abel summation identity. -/

open Real MeasureTheory
namespace Sude
noncomputable section

set_option backward.isDefEq.respectTransparency.types false in
/-- The lower endpoint 2 contributes `2 / log 2`; the logarithmic integral
is normalized to start at 2. -/
theorem odd_li_mainterm {x : ℝ} (hx : 2 ≤ x) :
    x / log x + (∫ t in (2 : ℝ)..x, (log t ^ 2)⁻¹) = liFromTwo x + 2 / log 2 := by
  have hd : ∀ t ∈ Set.uIcc 2 x,
      HasDerivAt (fun y : ℝ => liFromTwo y - y / log y) (log t ^ 2)⁻¹ t := by
    rw [Set.uIcc_of_le hx]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := ne_of_gt (log_pos (by linarith [ht.1]))
    have h1 := liFromTwo_hasDerivAt ht.1
    have h2 := (hasDerivAt_id t).div (Real.hasDerivAt_log ht0) hl
    have h2' : HasDerivAt (fun y : ℝ => y / log y)
        ((log t - t * t⁻¹) / log t ^ 2) t := by
      convert h2 using 1 <;> try rfl
      simp only [id_eq, one_mul]
    have he : (log t)⁻¹ - (log t - t * t⁻¹) / log t ^ 2 = (log t ^ 2)⁻¹ := by
      field_simp
      ring
    have hh := h1.sub h2'
    rw [he] at hh
    exact hh
  have hc : ContinuousOn (fun t : ℝ => (log t ^ 2)⁻¹) (Set.uIcc 2 x) := by
    rw [Set.uIcc_of_le hx]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : log t ≠ 0 := ne_of_gt (log_pos (by linarith [ht.1]))
    have hl2 : log t ^ 2 ≠ 0 := pow_ne_zero 2 hl
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  have hz : liFromTwo 2 = 0 := by simp [liFromTwo]
  rw [hz] at h
  linarith

end
end Sude
