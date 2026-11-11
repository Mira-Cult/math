import Sude.FWLogUpper

/-! Elementary scale improvement for BG's logarithmic range. This uses no
prime-count or theta hypothesis and does not establish a mean bound. -/
namespace Sude
noncomputable section

theorem bg_pow34_le_of_log_ge_24 {X : ℝ} (hX : 0 < X)
    (hlog : 24 ≤ Real.log X) : (2 : ℝ)^34 ≤ X := by
  by_contra h
  have hxlt : X < (2 : ℝ)^34 := lt_of_not_ge h
  have hlogX := Real.log_le_log hX hxlt.le
  rw [Real.log_pow] at hlogX
  have hlog2 : Real.log 2 < (7 : ℝ) / 10 := by linarith [Real.log_two_lt_d9]
  norm_num at hlogX
  linarith

theorem bg_sqrt_le_div_131072 {X : ℝ} (hX : 0 < X)
    (hlog : 24 ≤ Real.log X) : Real.sqrt X ≤ X / 131072 := by
  have hscale := bg_pow34_le_of_log_ge_24 hX hlog
  have hprod : 0 ≤ X * (X - 17179869184) := by
    apply mul_nonneg hX.le
    norm_num at hscale
    linarith
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · nlinarith

end
end Sude
