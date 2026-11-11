import Sude.FWPoolBound
import Sude.BGLogSqrtScale
import Sude.BMORPoolCorrelatedMean
import Sude.LiBGCoarseBase

/-! Coefficient-parametric error estimates for supplied pool scales.
No prime-counting input is introduced. -/

namespace Sude
noncomputable section

/-- Coarse error estimates for the actual pool with an arbitrary nonnegative
coefficient and supplied square-root scale. No count estimate is assumed. -/
theorem odd_count_mean_coarse_errors {n : ℕ} (hn : 0 < n)
    (hlog : 22 ≤ Real.log (poolMaximum n : ℝ))
    (hXbound : (2 : ℝ)^32 ≤ (poolMaximum n : ℝ))
    (C scale : ℝ) (hC : 0 ≤ C)
    (hsqrt : Real.sqrt (poolMaximum n : ℝ) ≤ (poolMaximum n : ℝ) / scale) :
    let N : ℝ := (n * n : ℕ)
    let X : ℝ := poolMaximum n
    let u : ℝ := Real.log X
    let q : ℝ := N / X
    let D : ℝ := C * (Real.sqrt X / u)
    let E : ℝ := (((poolMaximum n - 2 : ℕ) : ℝ) * D) / (N * X)
    let c : ℝ := C / scale
    D * u / X ≤ c ∧ E ≤ D / N ∧
    (0 ≤ liFromTwo 4 ∧ liFromTwo 4 ≤ 4) ∧
    D / N + E ≤ 2 * c / (u * q) ∧
    liFromTwo 4 / (N * X) ≤ 4 * u / ((2 ^ 32 : ℝ)^2 * (u * q)) ∧
    bgLiUpperNorm u / N ≤ (1 + 1/u + 4/u^2) / ((2 ^ 32 : ℝ) * (u * q)) := by
  dsimp only
  let N : ℝ := (n * n : ℕ)
  let X : ℝ := poolMaximum n
  let u : ℝ := Real.log X
  let q : ℝ := N / X
  let D : ℝ := C * (Real.sqrt X / u)
  let E : ℝ := (((poolMaximum n - 2 : ℕ) : ℝ) * D) / (N * X)
  let c : ℝ := C / scale
  have hX : (4294967296 : ℝ) ≤ X := by
    dsimp [X]
    norm_num at hXbound
    exact_mod_cast hXbound
  have hXp : 0 < X := by linarith
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n)
  have hu : 0 < u := by dsimp [u]; linarith
  have hq : 0 < q := div_pos hN hXp
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have he : D * u / X ≤ c := by
    dsimp [D, c]
    apply (div_le_iff₀ hXp).2
    have h : C * (Real.sqrt X / u) * u =
        C * Real.sqrt X := by field_simp
    rw [h]
    have hh := mul_le_mul_of_nonneg_left hsqrt hC
    have hdiv : C * (X / scale) = (C / scale) * X := by ring
    rw [hdiv] at hh
    exact hh
  have hE : E ≤ D / N := by
    dsimp [E]
    have hcast : (((poolMaximum n - 2 : ℕ) : ℝ)) ≤ X := by
      dsimp [X]; exact_mod_cast Nat.sub_le (poolMaximum n) 2
    have hp := mul_le_mul_of_nonneg_right hcast hD
    apply (div_le_iff₀ (mul_pos hN hXp)).2
    have hid : D / N * (N * X) = X * D := by field_simp
    rw [hid]
    nlinarith
  have hLi : 0 ≤ liFromTwo 4 ∧ liFromTwo 4 ≤ 4 := by
    constructor
    · have hm := liFromTwo_mono (show (2 : ℝ) ≤ 2 by norm_num) (show (2 : ℝ) ≤ 4 by norm_num)
      simpa [liFromTwo] using hm
    · have hm := liFromTwo_le_two_mul (show (2 : ℝ) ≤ 4 by norm_num)
      linarith
  have hDN : D / N ≤ c / (u * q) := by
    have h := div_le_div_of_nonneg_right he (le_of_lt (mul_pos hu hq))
    have hid : (D * u / X) / (u * q) = D / N := by
      dsimp [q]
      field_simp
    rw [hid] at h
    exact h
  have hsqX : (4294967296 : ℝ)^2 ≤ X^2 := by nlinarith
  have hLiBound : liFromTwo 4 / (N * X) ≤
      4 * u / ((2 ^ 32 : ℝ)^2 * (u * q)) := by
    have hmain : liFromTwo 4 / (N * X) ≤ 4 / (N * X) :=
      div_le_div_of_nonneg_right hLi.2 (mul_pos hN hXp).le
    have hx : 4 / (N * X) ≤ 4 / (q * (4294967296 : ℝ)^2) := by
      apply (div_le_div_iff₀ (mul_pos hN hXp) (mul_pos hq (by positivity))).2
      dsimp [q]
      field_simp
      nlinarith
    have hid : 4 / (q * (4294967296 : ℝ)^2) =
        4 * u / ((2 ^ 32 : ℝ)^2 * (u * q)) := by norm_num; field_simp
    exact hmain.trans (hid ▸ hx)
  have hBG : bgLiUpperNorm u / N ≤
      (1 + 1/u + 4/u^2) / ((2 ^ 32 : ℝ) * (u * q)) := by
    have hB : 0 ≤ 1 + 1/u + 4/u^2 := by positivity
    have heq : bgLiUpperNorm u / N = (1 + 1/u + 4/u^2) / (X * (u*q)) := by
      dsimp [bgLiUpperNorm, q]
      field_simp
    rw [heq]
    apply div_le_div_of_nonneg_left hB (by positivity)
    exact mul_le_mul_of_nonneg_right (by norm_num; exact hX) (mul_pos hu hq).le
  have hsum : D / N + E ≤ 2 * c / (u * q) := by
    calc
      D / N + E ≤ c / (u * q) + c / (u * q) := add_le_add hDN (hE.trans hDN)
      _ = 2 * c / (u * q) := by ring
  exact ⟨he, hE, hLi, hsum, hLiBound, hBG⟩

/-- FW order-index assumptions supply the scale 65536. -/
theorem odd_count_fw_pool_scales (lower : RSIndexLower) {n : ℕ}
    (hn : 19485 ≤ n) :
    (2 : ℝ)^32 ≤ (poolMaximum n : ℝ) ∧
      Real.sqrt (poolMaximum n : ℝ) ≤ (poolMaximum n : ℝ) / 65536 := by
  have hnat : 2 ^ 32 ≤ poolMaximum n := by
    have hh := le_of_lt (fw_poolMaximum_gt_four_seed lower hn)
    norm_num at hh ⊢
    exact hh
  have hX : (4294967296 : ℝ) ≤ (poolMaximum n : ℝ) := by exact_mod_cast hnat
  have hXp : (0 : ℝ) < poolMaximum n := by linarith
  constructor
  · norm_num
    exact_mod_cast hnat
  · have hprod : 0 ≤ (poolMaximum n : ℝ) * ((poolMaximum n : ℝ) - 4294967296) :=
      mul_nonneg hXp.le (by linarith)
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith

/-- BG's larger logarithm allows scale 131072, while retaining the same
2^32 lower bound for the separate Li endpoint charges. -/
theorem odd_count_bg_pool_scales {n : ℕ}
    (hlog : 24 ≤ Real.log (poolMaximum n : ℝ)) :
    (2 : ℝ)^32 ≤ (poolMaximum n : ℝ) ∧
      Real.sqrt (poolMaximum n : ℝ) ≤ (poolMaximum n : ℝ) / 131072 := by
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hbig := bg_pow34_le_of_log_ge_24 hX hlog
  constructor
  · norm_num at hbig ⊢
    exact le_trans (by norm_num) hbig
  · exact bg_sqrt_le_div_131072 hX hlog

end
end Sude
