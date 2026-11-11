import Sude.FWLogUpper
import Mathlib.Analysis.Real.Sqrt

/-! Elementary first-band logarithm and square-root score bounds. These
scalar bounds neither construct a witness nor assert a full-line budget. -/
namespace Sude
noncomputable section

/-- A uniform bound on the common logarithm in the bridge, wide, and seed
score invoices. -/
theorem fw_first_band_log_eight_le_thirteen {n : ℕ} (hnhi : n ≤ 35733) :
    Real.log (8 * (n : ℝ) + 8) ≤ 13 := by
  have hnR : (n : ℝ) ≤ 35733 := by exact_mod_cast hnhi
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hpos : (0 : ℝ) < 8 * (n : ℝ) + 8 := by positivity
  have hbound : (8 * (n : ℝ) + 8) ^ 2 ≤ (2 : ℝ) ^ 37 := by
    norm_num
    nlinarith
  have hlog := Real.log_le_log (pow_pos hpos 2) hbound
  rw [Real.log_pow, Real.log_pow] at hlog
  have hlog2 : Real.log 2 < (7 : ℝ) / 10 := by linarith [Real.log_two_lt_d9]
  norm_num at hlog
  linarith

/-- The bridge square-root factor is bounded independently of the square. -/
theorem fw_first_band_bridge_sqrt_le_35 {n : ℕ} (hnhi : n ≤ 35733) :
    Real.sqrt (94 * Real.log (8 * (n : ℝ) + 8)) ≤ 35 := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · have h := fw_first_band_log_eight_le_thirteen hnhi
    nlinarith

/-- The wide square-root factor uses the actual natural-division stage
count `n / 450` before coercion to the reals. -/
theorem fw_first_band_wide_sqrt_le_183 {n : ℕ} (hnhi : n ≤ 21248) :
    Real.sqrt ((54 * ((n / 450 : ℕ) : ℝ) + 4) * Real.log (8 * (n : ℝ) + 8)) ≤ 183 := by
  have hq : ((n / 450 : ℕ) : ℝ) ≤ 47 := by
    exact_mod_cast (show n / 450 ≤ 47 by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.log (8 * (n : ℝ) + 8) := by
    apply Real.log_nonneg
    linarith
  have hlog := fw_first_band_log_eight_le_thirteen (Nat.le_trans hnhi (by decide))
  have hfactor : (54 * ((n / 450 : ℕ) : ℝ) + 4) ≤ (54 * 47 + 4 : ℝ) := by
    linarith
  have hprod := mul_le_mul hfactor hlog hlog0 (by norm_num : (0 : ℝ) ≤ 54 * 47 + 4)
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · nlinarith

theorem fw_wide_sqrt_le_236 {n : ℕ} (hnhi : n ≤ 35733) :
    Real.sqrt ((54 * ((n / 450 : ℕ) : ℝ) + 4) * Real.log (8 * (n : ℝ) + 8)) ≤ 236 := by
  have hq : ((n / 450 : ℕ) : ℝ) ≤ 79 := by
    exact_mod_cast (show n / 450 ≤ 79 by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.log (8 * (n : ℝ) + 8) := by
    apply Real.log_nonneg
    linarith
  have hlog := fw_first_band_log_eight_le_thirteen hnhi
  have hfactor : (54 * ((n / 450 : ℕ) : ℝ) + 4) ≤ (54 * 79 + 4 : ℝ) := by
    linarith
  have hprod := mul_le_mul hfactor hlog hlog0 (by norm_num : (0 : ℝ) ≤ 54 * 79 + 4)
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · nlinarith

end
end Sude
