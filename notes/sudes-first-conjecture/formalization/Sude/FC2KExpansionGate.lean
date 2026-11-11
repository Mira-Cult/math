import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic

/-! The uniform large-cut numerical gate FC2K1. All logarithms are natural. -/
namespace Sude

/-- The finite controller's large-cut tail inequality holds throughout its
entire real domain, rather than only at sampled integer orders. -/
theorem fc2k_large_cut_gate {n : ℝ} (hn : 2001 ≤ n) :
    6 * Real.log (4 * n) + Real.log 8 < n / 34 := by
  have hnpos : 0 < n := by linarith
  have hlog2 : Real.log 2 < (7 : ℝ) / 10 := by
    linarith [Real.log_two_lt_d9]
  have h8004 : Real.log (8004 : ℝ) ≤ 13 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 8004)
      (by norm_num : (8004 : ℝ) ≤ 2 ^ 13)
    rw [Real.log_pow] at h
    norm_num at h ⊢
    exact h
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have h : (8 : ℝ) = 2 ^ 3 := by norm_num
    rw [h, Real.log_pow]
    norm_num
  have hratio : 0 < n / 2001 := by positivity
  have hlogratio : Real.log (n / 2001) ≤ n / 2001 - 1 :=
    Real.log_le_sub_one_of_pos hratio
  have hfactor : (4 : ℝ) * n = 8004 * (n / 2001) := by ring
  have hlog : Real.log (4 * n) = Real.log 8004 + Real.log (n / 2001) := by
    rw [hfactor, Real.log_mul (by norm_num) (ne_of_gt hratio)]
  rw [hlog, h8]
  linarith

/-- FC2K's conditioned small-cut entropy inequality, with the exact
rational constants from the source. -/
theorem fc2k_small_cut_gate :
    1 + 3 * Real.binEntropy ((199 : ℝ) / 1200) +
      (3 - (199 : ℝ) / 400 - 1) * Real.log (1 / 256) +
      3 * Real.log 3 < Real.log (1 / 8) := by
  have hlog2 : (69 : ℝ) / 100 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog3 : 5 * Real.log 3 ≤ 8 * Real.log 2 := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < 3 ^ 5)
      (by norm_num : (3 : ℝ) ^ 5 ≤ 2 ^ 8)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num at h
    linarith
  have hloga : 5 * Real.log ((199 : ℝ) / 1200)⁻¹ ≤ 13 * Real.log 2 := by
    have h := Real.log_le_log
      (by positivity : (0 : ℝ) < (((199 : ℝ) / 1200)⁻¹) ^ 5)
      (by norm_num : (((199 : ℝ) / 1200)⁻¹) ^ 5 ≤ 2 ^ 13)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num at h
    linarith
  have hlogb : Real.log (1 - (199 : ℝ) / 1200)⁻¹ ≤ (199 : ℝ) / 1001 := by
    have h := Real.log_le_sub_one_of_pos
      (by positivity : 0 < (1 - (199 : ℝ) / 1200)⁻¹)
    norm_num at h ⊢
    exact h
  have hentropy : Real.binEntropy ((199 : ℝ) / 1200) ≤
      (199 : ℝ) / 1200 * (13 / 5 * Real.log 2) + 199 / 1200 := by
    unfold Real.binEntropy
    nlinarith
  have h256 : Real.log ((1 : ℝ) / 256) = -8 * Real.log 2 := by
    have h : (1 : ℝ) / 256 = (2 ^ 8)⁻¹ := by norm_num
    rw [h, Real.log_inv, Real.log_pow]
    norm_num
  have h8 : Real.log ((1 : ℝ) / 8) = -3 * Real.log 2 := by
    have h : (1 : ℝ) / 8 = (2 ^ 3)⁻¹ := by norm_num
    rw [h, Real.log_inv, Real.log_pow]
    norm_num
  rw [h256, h8]
  linarith

/-- The entropy function used in FC2K's large-cut probability bound. -/
noncomputable def fc2kCutEntropy (t : ℝ) : ℝ :=
  3 * (t * Real.binEntropy ((199 : ℝ) / 1200) +
    (1 - t) * Real.binEntropy (((199 : ℝ) / 1200) * t / (1 - t))) -
      2 * Real.binEntropy t

/-- The right-hand FC2K entropy endpoint, proved by rational log bounds. -/
theorem fc2k_entropy_half_gate : fc2kCutEntropy (1 / 2) < -(1 : ℝ) / 34 := by
  have hlog2 : (693 : ℝ) / 1000 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hloga : 27 * Real.log ((199 : ℝ) / 1200)⁻¹ ≤ 70 * Real.log 2 := by
    have h := Real.log_le_log
      (by positivity : (0 : ℝ) < (((199 : ℝ) / 1200)⁻¹) ^ 27)
      (by norm_num : (((199 : ℝ) / 1200)⁻¹) ^ 27 ≤ 2 ^ 70)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num at h
    linarith
  have hlogb : Real.log (1 - (199 : ℝ) / 1200)⁻¹ ≤ 23 / 125 := by
    have hmono := Real.log_le_log
      (by positivity : (0 : ℝ) < (1 - (199 : ℝ) / 1200)⁻¹)
      (by norm_num : (1 - (199 : ℝ) / 1200)⁻¹ ≤ ((1023 : ℝ) / 1000) ^ 8)
    have htangent := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1023 / 1000)
    rw [Real.log_pow] at hmono
    norm_num at hmono htangent ⊢
    linarith
  have hentropy : Real.binEntropy ((199 : ℝ) / 1200) ≤
      (199 : ℝ) / 1200 * (70 / 27 * Real.log 2) + (1001 / 1200) * (23 / 125) := by
    unfold Real.binEntropy
    nlinarith
  have hhalf : Real.binEntropy ((1 : ℝ) / 2) = Real.log 2 := by
    simpa only [one_div] using Real.binEntropy_two_inv
  unfold fc2kCutEntropy
  have heq : ((199 : ℝ) / 1200) * (1 / 2) / (1 - 1 / 2) = 199 / 1200 := by norm_num
  rw [heq, hhalf]
  linarith

/-- The left-hand FC2K entropy endpoint. Rational tangent bounds and the
library's certified logarithm enclosures retain the small numerical margin. -/
theorem fc2k_entropy_small_gate : fc2kCutEntropy (1 / 256) < -(1 : ℝ) / 34 := by
  have hlog2lo : (6931471803 : ℝ) / 10000000000 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog2hi : Real.log 2 < (6931471808 : ℝ) / 10000000000 := by
    linarith [Real.log_two_lt_d9]
  have hlog3hi : Real.log 3 < (10986122888 : ℝ) / 10000000000 := by
    linarith [Real.log_three_lt_d9]
  have hloga : 5 * Real.log ((199 : ℝ) / 1200)⁻¹ ≤ 13 * Real.log 2 := by
    have h := Real.log_le_log
      (by positivity : (0 : ℝ) < (((199 : ℝ) / 1200)⁻¹) ^ 5)
      (by norm_num : (((199 : ℝ) / 1200)⁻¹) ^ 5 ≤ 2 ^ 13)
    rw [Real.log_pow, Real.log_pow] at h
    norm_num at h
    linarith
  have hlogb : Real.log (1 - (199 : ℝ) / 1200)⁻¹ ≤ (199 : ℝ) / 1001 := by
    have h := Real.log_le_sub_one_of_pos
      (by positivity : 0 < (1 - (199 : ℝ) / 1200)⁻¹)
    norm_num at h ⊢
    exact h
  have hHa : Real.binEntropy ((199 : ℝ) / 1200) ≤
      (199 : ℝ) / 1200 * (13 / 5 * Real.log 2) + 199 / 1200 := by
    unfold Real.binEntropy
    nlinarith
  have h1536 : Real.log (1536 : ℝ) = Real.log 3 + 9 * Real.log 2 := by
    have h : (1536 : ℝ) = 3 * 2 ^ 9 := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have h1538 : Real.log (1538 : ℝ) ≤ Real.log 3 + 9 * Real.log 2 + 1 / 768 := by
    have hratio := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1538 / 1536)
    have hfactor : (1538 : ℝ) = 1536 * (1538 / 1536) := by norm_num
    have hlog : Real.log (1538 : ℝ) = Real.log 1536 + Real.log (1538 / 1536) := by
      calc
        Real.log (1538 : ℝ) = Real.log (1536 * (1538 / 1536)) := congrArg Real.log hfactor
        _ = _ := Real.log_mul (by norm_num) (by norm_num)
    rw [h1536] at hlog
    norm_num at hratio
    linarith
  have hzlog : Real.log ((199 : ℝ) / 306000)⁻¹ ≤
      9 * Real.log 2 + Real.log 3 + 1 / 768 := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((199 : ℝ) / 306000)⁻¹)
      (by norm_num : ((199 : ℝ) / 306000)⁻¹ ≤ 1538)
    linarith
  have hzother : Real.log (1 - (199 : ℝ) / 306000)⁻¹ ≤
      (199 : ℝ) / 305801 := by
    have h := Real.log_le_sub_one_of_pos
      (by positivity : 0 < (1 - (199 : ℝ) / 306000)⁻¹)
    norm_num at h ⊢
    exact h
  have hHz : Real.binEntropy ((199 : ℝ) / 306000) ≤
      (199 : ℝ) / 306000 * (9 * Real.log 2 + Real.log 3 + 1 / 768) +
        199 / 306000 := by
    unfold Real.binEntropy
    nlinarith
  have htother : (1 : ℝ) / 256 ≤ Real.log (1 - (1 : ℝ) / 256)⁻¹ := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < 1 - (1 : ℝ) / 256)
    rw [Real.log_inv]
    linarith
  have htlog : Real.log ((1 : ℝ) / 256)⁻¹ = 8 * Real.log 2 := by
    have h : ((1 : ℝ) / 256)⁻¹ = 2 ^ 8 := by norm_num
    rw [h, Real.log_pow]
    norm_num
  have hHt : (1 : ℝ) / 256 * (8 * Real.log 2) +
      (255 / 256) * (1 / 256) ≤ Real.binEntropy (1 / 256) := by
    unfold Real.binEntropy
    rw [htlog]
    nlinarith
  unfold fc2kCutEntropy
  have heq : ((199 : ℝ) / 1200) * (1 / 256) / (1 - 1 / 256) = 199 / 306000 := by norm_num
  rw [heq]
  linarith

end Sude
