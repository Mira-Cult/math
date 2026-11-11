import Sude.LiBGCoarseBase
import Sude.LiBGGrowth
import Sude.LiBGExpDominance

/-! Unconditional BG logarithmic-integral comparisons on the log ≥ 22
range. The proof combines coarse elementary base bounds, derivative growth,
and exact exponential domination; no finite Li quadrature is assumed. -/

namespace Sude
noncomputable section

/-- For x ≥ 2 and log x ≥ 22 the BG lower and upper Li comparisons hold. -/
theorem bg_li_bounds_of_log_ge_22 {x : ℝ} (hx : 2 ≤ x)
    (hu : 22 ≤ Real.log x) :
    bgLiLower x < liFromTwo x ∧ liFromTwo x < bgLiUpper x := by
  have hxpos : 0 < x := by linarith
  have hhalfpos : 0 < x / 2 := by linarith
  have hloghalf : 6 ≤ Real.log (x / 2) := by
    rw [Real.log_div (ne_of_gt hxpos) (by norm_num : (2 : ℝ) ≠ 0)]
    linarith [Real.log_two_lt_d9]
  have hhalf : Real.exp 6 ≤ x / 2 := by
    have h := Real.exp_le_exp.mpr hloghalf
    simpa [Real.exp_log hhalfpos] using h
  have he : (2 : ℝ) ≤ Real.exp 6 := by linarith [Real.add_one_le_exp (6 : ℝ)]
  have hhalf2 : 2 ≤ x / 2 := he.trans hhalf
  have hmonoL := bg_lower_gap_monotone (show (2 : ℝ) ∈ Set.Ici 2 by simp) hhalf2 hhalf2
  have hmonoU := bg_upper_gap_monotone (show Real.exp 6 ∈ Set.Ici (Real.exp 6) by simp) hhalf hhalf
  have hbaseL := bg_lower_gap_at_two_gt
  have hbaseU := bg_upper_gap_at_exp_six_gt
  have hgrowthL := bgLiLower_gap_half_growth hx hu
  have hgrowthU := bgLiUpper_gap_half_growth hx hu
  have hlargeL := bg_lower_exp_dominance hu
  have hlargeU := bg_upper_exp_dominance hu
  rw [Real.exp_log hxpos] at hlargeL hlargeU
  constructor <;> linarith

end
end Sude
