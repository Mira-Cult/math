import Sude.BMORExplicitFormulaImports
import Sude.T75WheelPotential
import Sude.T75CompactBinning
import Sude.GlobalPoolMeanBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# T75 Prime Target Supplies for `2001 ≤ n ≤ 19483` (and Unbounded Explicit-Formula Theta Bounds)

From `BMORFiniteTheta`, `BMORExplicitFormulaImports`, `RSPrimeCountImports`, `RSIndexLowerSharp`,
and `RSIndexUpperSharp`, this module establishes:

1. `bmor_theta_mod_two_all_ge_7e12` and `bmor_theta_small_moduli_all_ge_7e12`:
   uniform explicit-formula Chebyshev `θ` bounds for **all `x ≥ 7 * 10^12` with no upper `log x` cap**
   (serving both `9301 ≤ n ≤ 19483` and the unbounded upper tail `n ≥ 35735`).
2. `fc2k_t75_targets_low`:
   prime row/column/diagonal target vector `f : Fin n → ℕ` across `2001 ≤ n ≤ 9299, Odd n`
   with uniform discrepancy `D = (23 / 50 : ℝ) * (poolMaximum n : ℝ)`.
3. `fc2k_t75_targets_high`:
   prime row/column/diagonal target vector `f : Fin n → ℕ` across `9301 ≤ n ≤ 19483, Odd n`
   with discrepancy `D = y / 400`.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-! ### Section 1: Unbounded-above explicit-formula `θ` bounds for `x ≥ 7 * 10^12` -/

private theorem pi_gt_314 : (314 / 100 : ℝ) < Real.pi := by
  have h := Real.pi_gt_d2
  norm_num at h ⊢
  exact h

private theorem pi_lt_315 : Real.pi < (315 / 100 : ℝ) := by
  have h := Real.pi_lt_d2
  norm_num at h ⊢
  exact h

private theorem log_two_gt_frac : (6931471803 / 10000000000 : ℝ) < Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  exact h

private theorem log_two_lt_frac : Real.log 2 < (6931471808 / 10000000000 : ℝ) := by
  have h := Real.log_two_lt_d9
  norm_num at h ⊢
  exact h

private theorem log_two_pi_add_one_ge_two :
    (2 : ℝ) ≤ Real.log (2 * Real.pi) + 1 := by
  have hpi : (314 / 100 : ℝ) < Real.pi := pi_gt_314
  have h4 : (2 : ℝ) ^ 2 ≤ 2 * Real.pi := by linarith
  have hlog4 : Real.log ((2 : ℝ) ^ 2) ≤ Real.log (2 * Real.pi) :=
    Real.log_le_log (by positivity) h4
  rw [Real.log_pow] at hlog4
  push_cast at hlog4
  linarith [log_two_gt_frac]

private theorem quad_diff_le_half (u : ℝ) :
    u - u ^ 2 / 2 ≤ (1 / 2 : ℝ) := by
  have hsq : 0 ≤ (u - 1) ^ 2 := sq_nonneg (u - 1)
  linarith

private theorem bmorLowZeroCap_mod_two_le :
    bmorLowZeroCap 2 (3 * 10 ^ 10 : ℝ) ≤ 105 := by
  unfold bmorLowZeroCap bmorC1 bmorC2
  dsimp only
  let ν := Real.log (2 : ℝ)
  let lam := Real.log (2 * (3 * 10 ^ 10 : ℝ))
  let c := Real.log (2 * Real.pi) + 1
  have hν_hi : ν ≤ 7 / 10 := by
    dsimp [ν]
    linarith [log_two_lt_frac]
  have hc_lo : (2 : ℝ) ≤ c := log_two_pi_add_one_ge_two
  have hlam_hi : lam ≤ 25 := by
    have hle : (2 * (3 * 10 ^ 10 : ℝ)) ≤ (2 : ℝ) ^ 36 := by norm_num
    have hlog := Real.log_le_log (by positivity) hle
    rw [Real.log_pow] at hlog
    dsimp [lam]
    push_cast at hlog
    linarith [log_two_lt_frac]
  have hlam_lo : c ≤ lam := by
    have hpi : Real.pi < (315 / 100 : ℝ) := pi_lt_315
    have he : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
    have h2pi_e : (2 * Real.pi) * Real.exp 1 ≤ 2 * (3 * 10 ^ 10 : ℝ) := by nlinarith
    have hlog := Real.log_le_log (by positivity) h2pi_e
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp] at hlog
    exact hlog
  have hquad1 : (ν - c) - (ν - c) ^ 2 / 2 ≤ 1 / 2 := quad_diff_le_half (ν - c)
  have hdiff_hi : lam - c ≤ 23 := by linarith
  have hdiff_lo : 0 ≤ lam - c := by linarith
  have hquad2 : (lam - c) + (lam - c) ^ 2 / 2 ≤ 23 + 23 ^ 2 / 2 := by nlinarith
  have hnum : (ν - c) + (lam - c) + ((lam - c) ^ 2 - (ν - c) ^ 2) / 2 ≤ 288 := by linarith
  have hpi_lo : (314 / 100 : ℝ) < Real.pi := pi_gt_314
  have hdiv : ((ν - c) + (lam - c) + ((lam - c) ^ 2 - (ν - c) ^ 2) / 2) / Real.pi ≤
      288 / (314 / 100 : ℝ) := by
    have h1 : ((ν - c) + (lam - c) + ((lam - c) ^ 2 - (ν - c) ^ 2) / 2) / Real.pi ≤
        288 / Real.pi := div_le_div_of_nonneg_right hnum (by positivity)
    have h2 : (288 : ℝ) / Real.pi ≤ 288 / (314 / 100 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (le_of_lt hpi_lo)
    exact h1.trans h2
  change ((ν - c) + (lam - c) + ((lam - c) ^ 2 - (ν - c) ^ 2) / 2) / Real.pi +
    2 * (399 / 1000) * ν + 399 / 1000 + 2 * (5338 / 1000) - (399 / 1000) / (3 * 10 ^ 10 : ℝ) ≤ 105
  linarith

private theorem bmorSmoothFactor_ten_le (τ : ℝ) (hτ_pos : 0 < τ) (hτ_hi : τ ≤ 1 / 10 ^ 5) :
    bmorSmoothFactor 10 τ ≤ (τ ^ 10)⁻¹ * 2048 := by
  unfold bmorSmoothFactor
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hterm : ∀ j ∈ Finset.range 11,
      (Nat.choose 10 j : ℝ) * (1 + (j : ℝ) * τ) ^ 11 ≤ (Nat.choose 10 j : ℝ) * 2 := by
    intro j hj
    have hj_lt : j < 11 := Finset.mem_range.mp hj
    have hj_le : (j : ℝ) ≤ 10 := by exact_mod_cast (show j ≤ 10 by omega)
    have h1 : 1 + (j : ℝ) * τ ≤ 1 + 10 * (1 / 10 ^ 5 : ℝ) := by nlinarith
    have hpow : (1 + (j : ℝ) * τ) ^ 11 ≤ (1 + 10 * (1 / 10 ^ 5 : ℝ)) ^ 11 :=
      pow_le_pow_left₀ (by positivity) h1 11
    have hpow2 : (1 + 10 * (1 / 10 ^ 5 : ℝ)) ^ 11 ≤ 2 := by norm_num
    exact mul_le_mul_of_nonneg_left (hpow.trans hpow2) (Nat.cast_nonneg _)
  have hsum_nat : (∑ j ∈ Finset.range 11, Nat.choose 10 j * 2) = 2048 := by decide
  have hsum_real : (∑ j ∈ Finset.range 11, (Nat.choose 10 j : ℝ) * 2) = 2048 := by
    exact_mod_cast hsum_nat
  exact (Finset.sum_le_sum hterm).trans (le_of_eq hsum_real)

private theorem log_ten_pow_eight_bounds :
    (18 : ℝ) ≤ Real.log (10 ^ 8 : ℝ) ∧ Real.log (10 ^ 8 : ℝ) ≤ 19 := by
  constructor
  · have hle : (2 : ℝ) ^ 26 ≤ 10 ^ 8 := by norm_num
    have h := Real.log_le_log (by positivity) hle
    rw [Real.log_pow] at h
    push_cast at h
    linarith [log_two_gt_frac]
  · have hle : (10 ^ 8 : ℝ) ≤ (2 : ℝ) ^ 27 := by norm_num
    have h := Real.log_le_log (by positivity) hle
    rw [Real.log_pow (2 : ℝ) 27] at h
    push_cast at h
    linarith [log_two_lt_frac]

private theorem bmorLowZeroCap_thirty_six_le :
    bmorLowZeroCap (36 : ℝ) ((10 ^ 8 : ℝ) / 36) ≤ 68 := by
  unfold bmorLowZeroCap bmorC1 bmorC2
  dsimp only
  let ν := Real.log (36 : ℝ)
  let lam := Real.log ((36 : ℝ) * ((10 ^ 8 : ℝ) / 36))
  let c := Real.log (2 * Real.pi) + 1
  have hν_hi : ν ≤ 5 := by
    have hle : (36 : ℝ) ≤ (2 : ℝ) ^ 6 := by norm_num
    have h := Real.log_le_log (by positivity) hle
    rw [Real.log_pow] at h
    dsimp [ν]
    push_cast at h
    linarith [log_two_lt_frac]
  have hc_lo : (2 : ℝ) ≤ c := log_two_pi_add_one_ge_two
  have hlam_eq : lam = Real.log (10 ^ 8 : ℝ) := by
    dsimp [lam]
    congr 1
    norm_num
  have hlam_hi : lam ≤ 19 := by
    rw [hlam_eq]
    exact log_ten_pow_eight_bounds.2
  have hlam_lo : c ≤ lam := by
    rw [hlam_eq]
    have := log_ten_pow_eight_bounds.1
    have hpi : Real.pi < (315 / 100 : ℝ) := pi_lt_315
    have h2pi : 2 * Real.pi ≤ (2 : ℝ) ^ 3 := by linarith
    have hlog := Real.log_le_log (by positivity) h2pi
    rw [Real.log_pow] at hlog
    dsimp [c]
    push_cast at hlog
    linarith [log_two_lt_frac]
  have hquad1 : (ν - c) - (ν - c) ^ 2 / 2 ≤ 1 / 2 := quad_diff_le_half (ν - c)
  have hdiff_hi : lam - c ≤ 17 := by linarith
  have hdiff_lo : 0 ≤ lam - c := by linarith
  have hquad2 : (lam - c) + (lam - c) ^ 2 / 2 ≤ 17 + 17 ^ 2 / 2 := by nlinarith
  have hnum : (ν - c) + (lam - c) + ((lam - c) ^ 2 - (ν - c) ^ 2) / 2 ≤ 162 := by linarith
  have hpi_lo : (314 / 100 : ℝ) < Real.pi := pi_gt_314
  have hdiv : ((ν - c) + (lam - c) + ((lam - c) ^ 2 - (ν - c) ^ 2) / 2) / Real.pi ≤
      162 / (314 / 100 : ℝ) := by
    have h1 : ((ν - c) + (lam - c) + ((lam - c) ^ 2 - (ν - c) ^ 2) / 2) / Real.pi ≤
        162 / Real.pi := div_le_div_of_nonneg_right hnum (by positivity)
    have h2 : (162 : ℝ) / Real.pi ≤ 162 / (314 / 100 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (le_of_lt hpi_lo)
    exact h1.trans h2
  change ((ν - c) + (lam - c) + ((lam - c) ^ 2 - (ν - c) ^ 2) / 2) / Real.pi +
    2 * (399 / 1000) * ν + 399 / 1000 + 2 * (5338 / 1000) - (399 / 1000) / ((10 ^ 8 : ℝ) / 36) ≤ 68
  linarith

/-- For all `x ≥ 7 * 10^12`, `25 * Real.log x + 62 ≤ (1 / 10) * Real.sqrt x` and `Real.sqrt x ≤ x / 2645751`
    and `28 ≤ Real.log x` (with no upper bound on `x` required). -/
private theorem sublinear_log_and_sqrt_ge_7e12 {x : ℝ} (hx : (7 * 10 ^ 12 : ℝ) ≤ x) :
    (28 : ℝ) ≤ Real.log x ∧
    25 * Real.log x + 62 ≤ (1 / 10 : ℝ) * Real.sqrt x ∧
    Real.sqrt x ≤ x / 2645751 := by
  have hx_pos : 0 < x := by linarith
  have hlog_lo : (28 : ℝ) ≤ Real.log x := by
    have h2_42 : (2 : ℝ) ^ 42 ≤ x := by linarith [show (2 : ℝ) ^ 42 ≤ 7 * 10 ^ 12 by norm_num]
    have h := Real.log_le_log (by positivity) h2_42
    rw [Real.log_pow] at h
    push_cast at h
    linarith [log_two_gt_frac]
  have hs_ge : (2645751 : ℝ) ≤ Real.sqrt x := by
    have hsq : (2645751 : ℝ) ^ 2 ≤ x := by linarith [show (2645751 : ℝ) ^ 2 ≤ 7 * 10 ^ 12 by norm_num]
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2645751)]
    exact Real.sqrt_le_sqrt hsq
  have hsqrt_le : Real.sqrt x ≤ x / 2645751 := by
    have hmul : (2645751 : ℝ) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
      mul_le_mul_of_nonneg_right hs_ge (Real.sqrt_nonneg x)
    rw [Real.mul_self_sqrt hx_pos.le] at hmul
    linarith
  let s := Real.sqrt x
  have hs_pos : 0 < s := by dsimp [s]; linarith
  let r := Real.sqrt s
  have hr_ge : (1626 : ℝ) ≤ r := by
    have hsq : (1626 : ℝ) ^ 2 ≤ s := by
      dsimp [s]
      linarith [show (1626 : ℝ) ^ 2 ≤ 2645751 by norm_num]
    dsimp [r]
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1626)]
    exact Real.sqrt_le_sqrt hsq
  have hr_pos : 0 < r := by linarith
  have hr_le : r ≤ s / 1626 := by
    have hmul : (1626 : ℝ) * r ≤ r * r := mul_le_mul_of_nonneg_right hr_ge hr_pos.le
    have hrr : r * r = s := Real.mul_self_sqrt hs_pos.le
    rw [hrr] at hmul
    linarith
  have hlog_r : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr_pos
  have hlog_s : Real.log s = 2 * Real.log r := by
    dsimp [r]
    rw [Real.log_sqrt hs_pos.le]
    ring
  have hlog_x : Real.log x = 2 * Real.log s := by
    dsimp [s]
    rw [Real.log_sqrt hx_pos.le]
    ring
  have h25 : 25 * Real.log x + 62 ≤ (1 / 10 : ℝ) * s := by
    linarith
  exact ⟨hlog_lo, h25, hsqrt_le⟩

/-- Uniform parity `θ` enclosure for ALL `x ≥ 7 * 10^12` (unbounded above):
    `|thetaAP x 2 1 - x| ≤ x / 24000`. -/
theorem bmor_theta_mod_two_all_ge_7e12
    (imp : BMORExplicitFormulaImports)
    {x : ℝ} (hx : (7 * 10 ^ 12 : ℝ) ≤ x) :
    |thetaAP x 2 1 - x| ≤ x / 24000 := by
  obtain ⟨hlog_lo, hlog_sub, hsqrt⟩ := sublinear_log_and_sqrt_ge_7e12 hx
  have hlogHs : Real.log (2 * (3 * 10 ^ 10 : ℝ)) ≤ 25 := by
    have hle : (2 * (3 * 10 ^ 10 : ℝ)) ≤ (2 : ℝ) ^ 36 := by norm_num
    have h := Real.log_le_log (by positivity) hle
    rw [Real.log_pow] at h
    push_cast at h
    linarith [log_two_lt_frac]
  have hpt := bmor_theta_mod_two_pointwise imp
    (rs := 10) (Hs := 3 * 10 ^ 10) (τs := 2 / 10 ^ 7) (zs := 28) (Ks := 105) (x := x)
    (by decide) (by norm_num) (by norm_num) hlogHs
    (by norm_num) (by norm_num) (by norm_num)
    bmorLowZeroCap_mod_two_le (by linarith) hlog_lo
  have hsmooth : bmorSmoothFactor 10 (2 / 10 ^ 7 : ℝ) ≤ ((2 / 10 ^ 7 : ℝ) ^ 10)⁻¹ * 2048 :=
    bmorSmoothFactor_ten_le (2 / 10 ^ 7 : ℝ) (by norm_num) (by norm_num)
  have hpar : bmorParityHighZeroSum (3 * 10 ^ 10 : ℝ) 10 ≤ ((3 * 10 ^ 10 : ℝ) ^ 10)⁻¹ * 1 := by
    unfold bmorParityHighZeroSum bmorC1 bmorC2
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hpi : (314 / 100 : ℝ) < Real.pi := pi_gt_314
    have hdiv : (25 / (10 : ℝ) + 1 / (10 : ℝ) ^ 2) / Real.pi ≤
        (25 / (10 : ℝ) + 1 / (10 : ℝ) ^ 2) / (314 / 100 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (le_of_lt hpi)
    norm_num at hdiv ⊢
    linarith
  have hpar_nonneg : 0 ≤ bmorParityHighZeroSum (3 * 10 ^ 10 : ℝ) 10 := by
    unfold bmorParityHighZeroSum bmorC1 bmorC2
    positivity
  have hprod_high : bmorSmoothFactor 10 (2 / 10 ^ 7 : ℝ) * bmorParityHighZeroSum (3 * 10 ^ 10 : ℝ) 10 ≤
      1 / 10 ^ 10 := by
    have h1 := mul_le_mul hsmooth hpar hpar_nonneg (by positivity)
    have h2 : (((2 / 10 ^ 7 : ℝ) ^ 10)⁻¹ * 2048) * (((3 * 10 ^ 10 : ℝ) ^ 10)⁻¹ * 1) ≤ 1 / 10 ^ 10 := by
      norm_num
    exact h1.trans h2
  have hmain : ((10 : ℝ) * (2 / 10 ^ 7 : ℝ) / 2 +
      bmorSmoothFactor 10 (2 / 10 ^ 7 : ℝ) * bmorParityHighZeroSum (3 * 10 ^ 10 : ℝ) 10) * x ≤
      (1 / 10 ^ 6 + 1 / 10 ^ 10) * x := by
    nlinarith
  norm_num at hpt
  linarith

/-- Uniform small-moduli `θ` enclosure for `3 ≤ q ≤ 36`, `φ(q) ≤ 12`, `gcd(q, a) = 1`,
    and ALL `x ≥ 7 * 10^12` (unbounded above):
    `φ(q) * |thetaAP x q a - x / φ(q)| ≤ x / 2700`. -/
theorem bmor_theta_small_moduli_all_ge_7e12
    (imp : BMORExplicitFormulaImports)
    {q : ℕ} {a : ℤ} {x : ℝ}
    (hq3 : 3 ≤ q) (hq36 : q ≤ 36) (hphi : (Nat.totient q : ℝ) ≤ 12)
    (hcop : Nat.Coprime q a.natAbs)
    (hx : (7 * 10 ^ 12 : ℝ) ≤ x) :
    (Nat.totient q : ℝ) * |thetaAP x q a - x / (Nat.totient q : ℝ)| ≤ x / 2700 := by
  obtain ⟨hlog_lo, hlog_sub, hsqrt⟩ := sublinear_log_and_sqrt_ge_7e12 hx
  obtain ⟨hlam_lo, hlam_hi⟩ := log_ten_pow_eight_bounds
  have har_lo : (9 : ℝ) ≤ (10 : ℝ) - 28 / (bmorZeroFreeR * (Real.log (10 ^ 8 : ℝ)) ^ 2) := by
    unfold bmorZeroFreeR
    have hsq : (18 : ℝ) ^ 2 ≤ (Real.log (10 ^ 8 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hlam_lo 2
    have hmul_sq : (28 / 5 : ℝ) * 18 ^ 2 ≤ (28 / 5 : ℝ) * (Real.log (10 ^ 8 : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)
    have hdiv : 28 / ((28 / 5 : ℝ) * (Real.log (10 ^ 8 : ℝ)) ^ 2) ≤ 28 / ((28 / 5 : ℝ) * 18 ^ 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hmul_sq
    linarith
  have hpt := bmor_theta_small_moduli_pointwise imp
    (q := q) (Q := 36) (a := a) (r := 10) (Φ := 12) (τ := 1 / 10 ^ 5) (z := 28) (K0 := 68) (x := x)
    hq3 hq36 (by decide) hcop hphi (by decide) (by norm_num) (by norm_num)
    (by norm_num) (by linarith) bmorLowZeroCap_thirty_six_le (by norm_num)
    (by linarith) hlog_lo
  have hsmooth : bmorSmoothFactor 10 (1 / 10 ^ 5 : ℝ) ≤ ((1 / 10 ^ 5 : ℝ) ^ 10)⁻¹ * 2048 :=
    bmorSmoothFactor_ten_le (1 / 10 ^ 5 : ℝ) (by norm_num) (by norm_num)
  have hhigh : bmorHighZeroSum (36 : ℝ) 12 28 10 ≤ (12 / (2 * ((10 ^ 8 : ℝ) / 36) ^ 10)) * 2 := by
    unfold bmorHighZeroSum bmorC1 bmorC2 bmorZeroFreeR
    dsimp only
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    let lam := Real.log (10 ^ 8 : ℝ)
    let ar := (10 : ℝ) - 28 / ((28 / 5 : ℝ) * lam ^ 2)
    have har9 : 9 ≤ ar := har_lo
    have har_sq : 81 ≤ ar ^ 2 := by nlinarith
    have hpi : (314 / 100 : ℝ) < Real.pi := pi_gt_314
    have hBr : (lam / ar + 1 / ar ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36) ≤ 1 := by
      have h1 : lam / ar ≤ 19 / 9 := by
        have ha : lam / ar ≤ 19 / ar := div_le_div_of_nonneg_right hlam_hi (by linarith)
        have hb : (19 : ℝ) / ar ≤ 19 / 9 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) har9
        exact ha.trans hb
      have h2 : 1 / ar ^ 2 ≤ 1 / 81 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) har_sq
      have h3 : (lam / ar + 1 / ar ^ 2) / Real.pi ≤ (19 / 9 + 1 / 81) / (314 / 100 : ℝ) := by
        have ha : (lam / ar + 1 / ar ^ 2) / Real.pi ≤ (19 / 9 + 1 / 81) / Real.pi :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        have hb : (19 / 9 + 1 / 81 : ℝ) / Real.pi ≤ (19 / 9 + 1 / 81) / (314 / 100 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) (le_of_lt hpi)
        exact ha.trans hb
      linarith
    have hBr0 : (lam / 10 + 1 / (10 : ℝ) ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36) ≤ 1 := by
      have h1 : (lam / 10 + 1 / (10 : ℝ) ^ 2) / Real.pi ≤ (19 / 10 + 1 / 100) / (314 / 100 : ℝ) := by
        have ha : (lam / 10 + 1 / (10 : ℝ) ^ 2) / Real.pi ≤ (19 / 10 + 1 / 100) / Real.pi :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        have hb : (19 / 10 + 1 / 100 : ℝ) / Real.pi ≤ (19 / 10 + 1 / 100) / (314 / 100 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) (le_of_lt hpi)
        exact ha.trans hb
      linarith
    have hexp1 : Real.exp (-28 / ((28 / 5 : ℝ) * lam)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith)
    have hexp2 : Real.exp (-28 / 2 : ℝ) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      norm_num
    have hBr_nonneg : 0 ≤ (lam / ar + 1 / ar ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36) := by
      have : 0 < ar := by linarith
      positivity
    have hBr0_nonneg : 0 ≤ (lam / 10 + 1 / (10 : ℝ) ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36) := by
      positivity
    have hprod1 : Real.exp (-28 / ((28 / 5 : ℝ) * lam)) *
        ((lam / ar + 1 / ar ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36)) ≤ 1 * 1 :=
      mul_le_mul hexp1 hBr hBr_nonneg (by norm_num)
    have hprod2 : Real.exp (-28 / 2 : ℝ) *
        ((lam / 10 + 1 / (10 : ℝ) ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36)) ≤ 1 * 1 :=
      mul_le_mul hexp2 hBr0 hBr0_nonneg (by norm_num)
    change Real.exp (-28 / ((28 / 5 : ℝ) * lam)) *
        ((lam / ar + 1 / ar ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36)) +
      Real.exp (-28 / 2 : ℝ) *
        ((lam / 10 + 1 / (10 : ℝ) ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36)) ≤ 2
    linarith
  have hhigh_nonneg : 0 ≤ bmorHighZeroSum (36 : ℝ) 12 28 10 := by
    unfold bmorHighZeroSum bmorC1 bmorC2 bmorZeroFreeR
    dsimp only
    have har_pos : 0 < (10 : ℝ) - 28 / ((28 / 5 : ℝ) * (Real.log (10 ^ 8 : ℝ)) ^ 2) := by
      unfold bmorZeroFreeR at har_lo
      linarith
    positivity
  have hprod_high : bmorSmoothFactor 10 (1 / 10 ^ 5 : ℝ) * bmorHighZeroSum (36 : ℝ) 12 28 10 ≤
      1 / 10 ^ 9 := by
    have h1 := mul_le_mul hsmooth hhigh hhigh_nonneg (by positivity)
    have h2 : (((1 / 10 ^ 5 : ℝ) ^ 10)⁻¹ * 2048) * ((12 / (2 * ((10 ^ 8 : ℝ) / 36) ^ 10)) * 2) ≤ 1 / 10 ^ 9 := by
      norm_num
    exact h1.trans h2
  have hmain : ((10 : ℝ) * (1 / 10 ^ 5 : ℝ) / 2 +
      bmorSmoothFactor 10 (1 / 10 ^ 5 : ℝ) * bmorHighZeroSum (36 : ℝ) 12 28 10) * x ≤
      (5 / 10 ^ 5 + 1 / 10 ^ 9) * x := by
    nlinarith
  norm_num at hpt
  linarith

private theorem bmor_theta_small_moduli_signed_ge_7e12
    (imp : BMORExplicitFormulaImports)
    {q : ℕ} {a : ℤ} {x : ℝ}
    (hq3 : 3 ≤ q) (hq36 : q ≤ 36) (hphi : (Nat.totient q : ℝ) ≤ 12)
    (hcop : Nat.Coprime q a.natAbs)
    (hx : (7 * 10 ^ 12 : ℝ) ≤ x) :
    |(Nat.totient q : ℝ) * thetaAP x q a - x| ≤ x / 2700 := by
  have h := bmor_theta_small_moduli_all_ge_7e12 imp hq3 hq36 hphi hcop hx
  have hphi_pos : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have heq : |(Nat.totient q : ℝ) * thetaAP x q a - x| =
      (Nat.totient q : ℝ) * |thetaAP x q a - x / (Nat.totient q : ℝ)| := by
    have h1 : (Nat.totient q : ℝ) * thetaAP x q a - x =
        (Nat.totient q : ℝ) * (thetaAP x q a - x / (Nat.totient q : ℝ)) := by
      field_simp
    rw [h1, abs_mul, abs_of_pos hphi_pos]
  rwa [← heq] at h

/-! ### Section 2: Shared interval-counting and favorable-gap helpers -/

private theorem thetaAP_sub_le_card_mul_log_local (a b : ℝ) (q : ℕ) (r : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    thetaAP b q r - thetaAP a q r ≤ ((apInterval a b q r).card : ℝ) * Real.log b := by
  rw [thetaAP_sub_eq_interval_sum a b q r hab]
  calc
    (∑ p ∈ apInterval a b q r, Real.log (p : ℝ))
      ≤ ∑ _p ∈ apInterval a b q r, Real.log b := by
        apply Finset.sum_le_sum
        intro p hp
        have ⟨_, _, hb_le, _⟩ := (mem_apInterval_iff a b q r (by linarith) (by linarith) p).mp hp
        exact Real.log_le_log (by linarith) hb_le
    _ = ((apInterval a b q r).card : ℝ) * Real.log b := by
        simp [nsmul_eq_mul]

private theorem favorable_gap_basic_props :
    ∀ h ∈ t75FavorableGaps, 2 ≤ h ∧ h ≤ 42 ∧ 2 * Nat.totient h ≤ h := by
  decide

private theorem favorable_gap_nat_props :
    ∀ h ∈ t75FavorableGaps, h ≠ 2 →
      let q := if h = 42 then 21 else h
      3 ≤ q ∧ q ≤ 36 ∧
      Nat.totient q ≤ 12 ∧ Nat.totient h = Nat.totient q ∧
      (∀ r ∈ Finset.range h, Nat.Coprime r h → Nat.Coprime q (r % q)) := by
  decide

private theorem favorable_gap_reduced_modulus {h r : ℕ}
    (hh : h ∈ t75FavorableGaps) (hne2 : h ≠ 2) (hr : r < h) (hcop : Nat.Coprime r h) :
    ∃ q : ℕ, q = (if h = 42 then 21 else h) ∧
      3 ≤ q ∧ q ≤ 36 ∧
      (Nat.totient q : ℝ) ≤ 12 ∧
      (Nat.totient h : ℝ) = (Nat.totient q : ℝ) ∧
      Nat.Coprime q ((r % q : ℕ) : ℤ).natAbs := by
  have hp := favorable_gap_nat_props h hh hne2
  dsimp only at hp
  let q := if h = 42 then 21 else h
  have hcop_nat : Nat.Coprime q (r % q) := hp.2.2.2.2 r (Finset.mem_range.mpr hr) hcop
  have hcop_int : Nat.Coprime q ((r % q : ℕ) : ℤ).natAbs := by
    rwa [Int.natAbs_natCast]
  refine ⟨q, rfl, hp.1, hp.2.1, ?_, ?_, hcop_int⟩
  · exact_mod_cast hp.2.2.1
  · exact_mod_cast hp.2.2.2.1

/-! ### Section 3: Sharp `poolMaximum` envelopes on `[2001, 19483]` -/

private theorem poolMaximum_gt_16278_sq (sharp : RSIndexLowerSharp) {n : ℕ} (hn : 2001 ≤ n) :
    (16278 / 1000 : ℝ) * (n : ℝ) ^ 2 < (poolMaximum n : ℝ) := by
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hj : (4004002 : ℝ) ≤ j := by
    dsimp [j]
    push_cast
    nlinarith [show (2001 : ℝ) ≤ n by exact_mod_cast hn]
  have hjpos : 0 < j := by linarith
  have hjpow : (2 : ℝ) ^ 219 < j ^ 10 :=
    lt_of_lt_of_le (by norm_num) (pow_le_pow_left₀ (by norm_num) hj 10)
  have hlogj : (15179 / 1000 : ℝ) < Real.log j := by
    have h := Real.log_lt_log (by positivity) hjpow
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith [log_two_gt_frac]
  have hllpow : (2 : ℝ) ^ 15 < (Real.log j) ^ 4 :=
    lt_of_lt_of_le (by norm_num) (pow_le_pow_left₀ (by norm_num) hlogj.le 4)
  have hloglogj : (2599 / 1000 : ℝ) < Real.log (Real.log j) := by
    have h := Real.log_lt_log (by positivity) hllpow
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith [log_two_gt_frac]
  have hsource : j * (Real.log j + Real.log (Real.log j) - 3 / 2) < (poolMaximum n : ℝ) := by
    have hn2 : 2 ≤ n * n + 1 := by nlinarith
    simpa [j, poolMaximum] using sharp (n * n + 1) hn2
  have hfac : (16278 / 1000 : ℝ) < Real.log j + Real.log (Real.log j) - 3 / 2 := by linarith
  have hmul := mul_lt_mul_of_pos_left hfac hjpos
  dsimp [j] at hsource hmul
  push_cast at hsource hmul
  nlinarith

private theorem poolMaximum_gt_1712_sq_ge_3001 (sharp : RSIndexLowerSharp) {n : ℕ} (hn : 3001 ≤ n) :
    (1712 / 100 : ℝ) * (n : ℝ) ^ 2 < (poolMaximum n : ℝ) := by
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hj : (9006002 : ℝ) ≤ j := by
    dsimp [j]
    push_cast
    nlinarith [show (3001 : ℝ) ≤ n by exact_mod_cast hn]
  have hjpos : 0 < j := by linarith
  have hjpow : (2 : ℝ) ^ 23 < j := lt_of_lt_of_le (by norm_num) hj
  have hlogj : (1594 / 100 : ℝ) < Real.log j := by
    have h := Real.log_lt_log (by positivity) hjpow
    rw [Real.log_pow] at h
    push_cast at h
    linarith [log_two_gt_frac]
  have hllpow : (2 : ℝ) ^ 31 < (Real.log j) ^ 8 :=
    lt_of_lt_of_le (by norm_num) (pow_le_pow_left₀ (by norm_num) hlogj.le 8)
  have hloglogj : (268 / 100 : ℝ) < Real.log (Real.log j) := by
    have h := Real.log_lt_log (by positivity) hllpow
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith [log_two_gt_frac]
  have hsource : j * (Real.log j + Real.log (Real.log j) - 3 / 2) < (poolMaximum n : ℝ) := by
    have hn2 : 2 ≤ n * n + 1 := by nlinarith
    simpa [j, poolMaximum] using sharp (n * n + 1) hn2
  have hfac : (1712 / 100 : ℝ) < Real.log j + Real.log (Real.log j) - 3 / 2 := by linarith
  have hmul := mul_lt_mul_of_pos_left hfac hjpos
  dsimp [j] at hsource hmul
  push_cast at hsource hmul
  nlinarith

private theorem poolMaximum_gt_ge_9301 (sharp : RSIndexLowerSharp) {n : ℕ} (hn : 9301 ≤ n) :
    (86508602 : ℝ) * (1954 / 100 : ℝ) < (poolMaximum n : ℝ) := by
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hj : (86508602 : ℝ) ≤ j := by
    dsimp [j]
    push_cast
    nlinarith [show (9301 : ℝ) ≤ n by exact_mod_cast hn]
  have hjpos : 0 < j := by linarith
  have hjpow : (2 : ℝ) ^ 105 < j ^ 4 :=
    lt_of_lt_of_le (by norm_num) (pow_le_pow_left₀ (by norm_num) hj 4)
  have hlogj : (1819 / 100 : ℝ) < Real.log j := by
    have h := Real.log_lt_log (by positivity) hjpow
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith [log_two_gt_frac]
  have hllpow : (2 : ℝ) ^ 33 < (Real.log j) ^ 8 :=
    lt_of_lt_of_le (by norm_num) (pow_le_pow_left₀ (by norm_num) hlogj.le 8)
  have hloglogj : (285 / 100 : ℝ) < Real.log (Real.log j) := by
    have h := Real.log_lt_log (by positivity) hllpow
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith [log_two_gt_frac]
  have hsource : j * (Real.log j + Real.log (Real.log j) - 3 / 2) < (poolMaximum n : ℝ) := by
    have hn2 : 2 ≤ n * n + 1 := by nlinarith
    simpa [j, poolMaximum] using sharp (n * n + 1) hn2
  have hfac : (1954 / 100 : ℝ) < Real.log j + Real.log (Real.log j) - 3 / 2 := by linarith
  have hmul := mul_lt_mul_of_pos_left hfac hjpos
  nlinarith

private theorem poolMaximum_upper_le_2299 (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 2001 ≤ n) (hnhi : n ≤ 2299) :
    (poolMaximum n : ℝ) < (5285402 : ℝ) * (1828 / 100 : ℝ) := by
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hjpos : 0 < j := by dsimp [j]; positivity
  have hjone : 1 < j := by
    dsimp [j]; push_cast; nlinarith [show (2001 : ℝ) ≤ n by exact_mod_cast hnlo]
  have hjhi : j ≤ 5285402 := by
    dsimp [j]; push_cast; nlinarith [show (n : ℝ) ≤ 2299 by exact_mod_cast hnhi]
  have hjpow : j ≤ (2 : ℝ) ^ 23 := hjhi.trans (by norm_num)
  have hlogj : Real.log j < 16 := by
    have h := Real.log_le_log hjpos hjpow
    rw [Real.log_pow] at h
    push_cast at h
    linarith [log_two_lt_frac]
  have hloglogj : Real.log (Real.log j) < 278 / 100 := by
    have h := Real.log_le_log (Real.log_pos hjone) hlogj.le
    rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, Real.log_pow] at h
    push_cast at h
    linarith [log_two_lt_frac]
  have hu : (poolMaximum n : ℝ) < j * (Real.log j + Real.log (Real.log j) - 1 / 2) := by
    have hn2 : 20 ≤ n * n + 1 := by nlinarith
    simpa [j, poolMaximum] using upperSharp (n * n + 1) hn2
  have hfac : Real.log j + Real.log (Real.log j) - 1 / 2 < 1828 / 100 := by linarith
  have hmul := mul_lt_mul_of_pos_left hfac hjpos
  nlinarith

private theorem poolMaximum_upper_le_3000 (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 2001 ≤ n) (hnhi : n ≤ 3000) :
    (poolMaximum n : ℝ) < (9000001 : ℝ) * (39 / 2 : ℝ) := by
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hjpos : 0 < j := by dsimp [j]; positivity
  have hjone : 1 < j := by
    dsimp [j]; push_cast; nlinarith [show (2001 : ℝ) ≤ n by exact_mod_cast hnlo]
  have hjhi : j ≤ 9000001 := by
    dsimp [j]; push_cast; nlinarith [show (n : ℝ) ≤ 3000 by exact_mod_cast hnhi]
  have hjpow : j ≤ (2 : ℝ) ^ 24 := hjhi.trans (by norm_num)
  have hlogj : Real.log j < 17 := by
    have h := Real.log_le_log hjpos hjpow
    rw [Real.log_pow] at h
    push_cast at h
    linarith [log_two_lt_frac]
  have hllpow : (Real.log j) ^ 4 ≤ (2 : ℝ) ^ 17 :=
    (pow_le_pow_left₀ (Real.log_pos hjone).le hlogj.le 4).trans (by norm_num)
  have hloglogj : Real.log (Real.log j) < 3 := by
    have h := Real.log_le_log (pow_pos (Real.log_pos hjone) 4) hllpow
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith [log_two_lt_frac]
  have hu : (poolMaximum n : ℝ) < j * (Real.log j + Real.log (Real.log j) - 1 / 2) := by
    have hn2 : 20 ≤ n * n + 1 := by nlinarith
    simpa [j, poolMaximum] using upperSharp (n * n + 1) hn2
  have hfac : Real.log j + Real.log (Real.log j) - 1 / 2 < 39 / 2 := by linarith
  have hmul := mul_lt_mul_of_pos_left hfac hjpos
  nlinarith

private theorem poolMaximum_upper_le_9299 (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 2001 ≤ n) (hnhi : n ≤ 9299) :
    (poolMaximum n : ℝ) < (86471402 : ℝ) * (2162 / 100 : ℝ) := by
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hjpos : 0 < j := by dsimp [j]; positivity
  have hjone : 1 < j := by
    dsimp [j]; push_cast; nlinarith [show (2001 : ℝ) ≤ n by exact_mod_cast hnlo]
  have hjhi : j ≤ 86471402 := by
    dsimp [j]; push_cast; nlinarith [show (n : ℝ) ≤ 9299 by exact_mod_cast hnhi]
  have hjpow : j ≤ (2 : ℝ) ^ 27 := hjhi.trans (by norm_num)
  have hlogj : Real.log j < 19 := by
    have h := Real.log_le_log hjpos hjpow
    rw [Real.log_pow] at h
    push_cast at h
    linarith [log_two_lt_frac]
  have hllpow : (Real.log j) ^ 2 ≤ (2 : ℝ) ^ 9 :=
    (pow_le_pow_left₀ (Real.log_pos hjone).le hlogj.le 2).trans (by norm_num)
  have hloglogj : Real.log (Real.log j) < 312 / 100 := by
    have h := Real.log_le_log (pow_pos (Real.log_pos hjone) 2) hllpow
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith [log_two_lt_frac]
  have hu : (poolMaximum n : ℝ) < j * (Real.log j + Real.log (Real.log j) - 1 / 2) := by
    have hn2 : 20 ≤ n * n + 1 := by nlinarith
    simpa [j, poolMaximum] using upperSharp (n * n + 1) hn2
  have hfac : Real.log j + Real.log (Real.log j) - 1 / 2 < 2162 / 100 := by linarith
  have hmul := mul_lt_mul_of_pos_left hfac hjpos
  nlinarith

private theorem poolMaximum_upper_le_19483 (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 9301 ≤ n) (hnhi : n ≤ 19483) :
    (poolMaximum n : ℝ) < (379587290 : ℝ) * (2362 / 100 : ℝ) := by
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hjpos : 0 < j := by dsimp [j]; positivity
  have hjone : 1 < j := by
    dsimp [j]; push_cast; nlinarith [show (9301 : ℝ) ≤ n by exact_mod_cast hnlo]
  have hjhi : j ≤ 379587290 := by
    dsimp [j]; push_cast; nlinarith [show (n : ℝ) ≤ 19483 by exact_mod_cast hnhi]
  have hjpow : j ≤ (2 : ℝ) ^ 29 := hjhi.trans (by norm_num)
  have hlogj : Real.log j < 21 := by
    have h := Real.log_le_log hjpos hjpow
    rw [Real.log_pow] at h
    push_cast at h
    linarith [log_two_lt_frac]
  have hllpow : (Real.log j) ^ 2 ≤ (2 : ℝ) ^ 9 :=
    (pow_le_pow_left₀ (Real.log_pos hjone).le hlogj.le 2).trans (by norm_num)
  have hloglogj : Real.log (Real.log j) < 312 / 100 := by
    have h := Real.log_le_log (pow_pos (Real.log_pos hjone) 2) hllpow
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith [log_two_lt_frac]
  have hu : (poolMaximum n : ℝ) < j * (Real.log j + Real.log (Real.log j) - 1 / 2) := by
    have hn2 : 20 ≤ n * n + 1 := by nlinarith
    simpa [j, poolMaximum] using upperSharp (n * n + 1) hn2
  have hfac : Real.log j + Real.log (Real.log j) - 1 / 2 < 2362 / 100 := by linarith
  have hmul := mul_lt_mul_of_pos_left hfac hjpos
  nlinarith

/-! ### Section 4: Low Regime (`2001 ≤ n ≤ 9299`, `D = (23 / 50) * X`) -/

private theorem bmor_finite_theta_increment_lower
    (bmor : BMORFiniteTheta) {h r : ℕ}
    (hh : h ∈ t75FavorableGaps) (hr : r < h) (hcop : Nat.Coprime r h)
    {u v : ℝ} (hu2 : 2 ≤ u) (huv : u ≤ v) (hv_cap : v ≤ (10 ^ 13 : ℝ)) :
    (Nat.totient h : ℝ) * (thetaAP v h (r : ℤ) - thetaAP u h (r : ℤ)) ≥
      (v - u) - 2 * 12 * (259 / 125 : ℝ) * Real.sqrt v := by
  have hsqrt_uv : Real.sqrt u ≤ Real.sqrt v := Real.sqrt_le_sqrt huv
  by_cases h2 : h = 2
  · subst h
    have hr1 : r = 1 := by
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · exact False.elim (absurd hcop (by decide))
      · rfl
    subst r
    have htu := abs_le.mp (bmor_theta_two_via_four bmor u (by linarith) (huv.trans (hv_cap.trans (by norm_num))))
    have htv := abs_le.mp (bmor_theta_two_via_four bmor v (by linarith) (hv_cap.trans (by norm_num)))
    have htot2 : (Nat.totient 2 : ℝ) = 1 := by norm_num
    rw [htot2]
    push_cast
    linarith [Real.sqrt_nonneg v]
  · obtain ⟨q, hq_def, hq3, hq36, hphi12, hphi_eq, hcop_q⟩ :=
      favorable_gap_reduced_modulus hh h2 hr hcop
    have hphi_pos : (0 : ℝ) < (Nat.totient q : ℝ) :=
      Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
    have htu := abs_le.mp (bmor_theta_bounded bmor q ((r % q : ℕ) : ℤ) u hq3 (by omega) hcop_q
      (by linarith) (huv.trans hv_cap))
    have htv := abs_le.mp (bmor_theta_bounded bmor q ((r % q : ℕ) : ℤ) v hq3 (by omega) hcop_q
      (by linarith) hv_cap)
    have hmul_u : (Nat.totient q : ℝ) * thetaAP u q ((r % q : ℕ) : ℤ) ≤
        u + (Nat.totient q : ℝ) * ((259 / 125 : ℝ) * Real.sqrt u) := by
      have hm := mul_le_mul_of_nonneg_left htu.2 hphi_pos.le
      have hc : (Nat.totient q : ℝ) * (u / (Nat.totient q : ℝ)) = u :=
        mul_div_cancel₀ u hphi_pos.ne'
      linarith
    have hmul_v : v - (Nat.totient q : ℝ) * ((259 / 125 : ℝ) * Real.sqrt v) ≤
        (Nat.totient q : ℝ) * thetaAP v q ((r % q : ℕ) : ℤ) := by
      have hm := mul_le_mul_of_nonneg_left htv.1 hphi_pos.le
      have hc : (Nat.totient q : ℝ) * (v / (Nat.totient q : ℝ)) = v :=
        mul_div_cancel₀ v hphi_pos.ne'
      linarith
    have herr_u : (Nat.totient q : ℝ) * ((259 / 125 : ℝ) * Real.sqrt u) ≤
        12 * ((259 / 125 : ℝ) * Real.sqrt v) := by
      have h1 : (Nat.totient q : ℝ) * ((259 / 125 : ℝ) * Real.sqrt u) ≤
          (Nat.totient q : ℝ) * ((259 / 125 : ℝ) * Real.sqrt v) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqrt_uv (by norm_num)) hphi_pos.le
      have h2 : (Nat.totient q : ℝ) * ((259 / 125 : ℝ) * Real.sqrt v) ≤
          12 * ((259 / 125 : ℝ) * Real.sqrt v) :=
        mul_le_mul_of_nonneg_right hphi12 (by positivity)
      exact h1.trans h2
    have herr_v : (Nat.totient q : ℝ) * ((259 / 125 : ℝ) * Real.sqrt v) ≤
        12 * ((259 / 125 : ℝ) * Real.sqrt v) :=
      mul_le_mul_of_nonneg_right hphi12 (by positivity)
    have hinc_eq : thetaAP v h (r : ℤ) - thetaAP u h (r : ℤ) =
        thetaAP v q ((r % q : ℕ) : ℤ) - thetaAP u q ((r % q : ℕ) : ℤ) := by
      by_cases h42 : h = 42
      · subst h
        rw [hq_def, if_pos rfl]
        exact thetaAP_forty_two_increment_eq_twenty_one hu2 huv hr hcop
      · rw [hq_def, if_neg h42, Nat.mod_eq_of_lt hr]
    rw [hinc_eq, hphi_eq]
    linarith

/-- T75 prime target vector across `2001 ≤ n ≤ 9299, Odd n` with uniform `D = (23 / 50) * X`. -/
theorem fc2k_t75_targets_low
    (bmor : BMORFiniteTheta) (rs : RSPrimeCountImports)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 2001 ≤ n) (hnhi : n ≤ 9299) (hn : Odd n) :
    let y : ℝ := (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let D : ℝ := (23 / 50 : ℝ) * (poolMaximum n : ℝ)
    ∃ f : Fin n → ℕ,
      (∑ i, f i) = Lucas.poolTotal n ∧
      (∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ) - y| ≤ D) := by
  dsimp only
  let X : ℝ := poolMaximum n
  let y : ℝ := (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue
  let D : ℝ := (23 / 50 : ℝ) * X
  have hX65 : (65170000 : ℝ) < X :=
    Nat.cast_lt.mpr (poolMaximum_gt_65170000_and_log_gt sharp hnlo).1
  have hXpos : 0 < X := by linarith
  have hm_bounds := global_pool_mean_bounds rs sharp hnlo
  have hN_pos : (0 : ℝ) < ((n * n : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos (by omega) (by omega)
  have hm_lo : (449 / 1000 : ℝ) * X < centralEntriesMean (prescribedPoolValues n) centralPoolValue := by
    rw [prescribedPoolValues_mean]
    exact (lt_div_iff₀ hXpos).mp hm_bounds.1
  have hm_hi : centralEntriesMean (prescribedPoolValues n) centralPoolValue < (519 / 1000 : ℝ) * X := by
    rw [prescribedPoolValues_mean]
    exact (div_lt_iff₀ hXpos).mp hm_bounds.2
  have hnloR : (2001 : ℝ) ≤ n := by exact_mod_cast hnlo
  have hnhiR : (n : ℝ) ≤ 9299 := by exact_mod_cast hnhi
  have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hy_lo : 2001 * ((449 / 1000 : ℝ) * X) ≤ y := by
    dsimp [y]
    exact mul_le_mul hnloR hm_lo.le (by positivity) hn_nonneg
  have hyD_linear : y + D ≤ ((519 / 1000 : ℝ) * n + 23 / 50) * X := by
    have hy1 : y ≤ (n : ℝ) * ((519 / 1000 : ℝ) * X) := by
      dsimp [y]
      exact mul_le_mul_of_nonneg_left hm_hi.le hn_nonneg
    dsimp [D]
    linarith
  have hyD_gt_two : (2 : ℝ) < y - D := by dsimp [D]; linarith
  have hX_hi9299 : X < (86471402 : ℝ) * (2162 / 100 : ℝ) :=
    poolMaximum_upper_le_9299 upperSharp hnlo hnhi
  have hyD_1e13 : y + D ≤ (10 ^ 13 : ℝ) := by
    have hcoef : (519 / 1000 : ℝ) * n + 23 / 50 ≤ (519 / 1000 : ℝ) * 9299 + 23 / 50 := by linarith
    have hm1 := mul_le_mul hcoef hX_hi9299.le hXpos.le (by positivity)
    linarith
  have hyD_2_44 : y + D ≤ (2 : ℝ) ^ 44 := by
    have hcoef : (519 / 1000 : ℝ) * n + 23 / 50 ≤ (519 / 1000 : ℝ) * 9299 + 23 / 50 := by linarith
    have hm1 := mul_le_mul hcoef hX_hi9299.le hXpos.le (by positivity)
    linarith
  have hsqrt_250 : Real.sqrt (y + D) ≤ X / 250 := by
    have hX_sq := poolMaximum_gt_16278_sq sharp hnlo
    have hlin : (250 : ℝ) ^ 2 * ((519 / 1000 : ℝ) * n + 23 / 50) ≤ X := by
      change (16278 / 1000 : ℝ) * (n : ℝ) ^ 2 < X at hX_sq
      nlinarith
    have hsq : y + D ≤ (X / 250) ^ 2 := by
      have hm := mul_le_mul_of_nonneg_right hlin hXpos.le
      have hid : ((250 : ℝ) ^ 2 * ((519 / 1000 : ℝ) * n + 23 / 50)) * X =
          ((519 / 1000 : ℝ) * n + 23 / 50) * X * (250 : ℝ) ^ 2 := by ring
      nlinarith
    calc
      Real.sqrt (y + D) ≤ Real.sqrt ((X / 250) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = X / 250 := Real.sqrt_sq (by positivity)

  have hD_pos : 0 < D := by dsimp [D]; positivity
  have hyD_pos : 0 < y + D := by linarith
  -- Seed pair and central density via 2-way split n ≤ 3000 vs 3001 ≤ n ≤ 9299
  have henv : ∃ (S_denom L_hi : ℝ),
      (S_denom = 250 ∧ L_hi = 2704 / 100 ∨ S_denom = 310 ∧ L_hi = 61 / 2) ∧
      Real.sqrt (y + D) ≤ X / S_denom ∧
      Real.log (y + D) ≤ L_hi := by
    by_cases h3000 : n ≤ 3000
    · have hX3000 := poolMaximum_upper_le_3000 upperSharp hnlo h3000
      have hn3000R : (n : ℝ) ≤ 3000 := by exact_mod_cast h3000
      have hyD_2_39 : y + D ≤ (2 : ℝ) ^ 39 := by
        have hcoef : (519 / 1000 : ℝ) * n + 23 / 50 ≤ (519 / 1000 : ℝ) * 3000 + 23 / 50 := by linarith
        have hm1 := mul_le_mul hcoef hX3000.le hXpos.le (by positivity)
        linarith
      have hlog39 : Real.log (y + D) ≤ 2704 / 100 := by
        have h := Real.log_le_log hyD_pos hyD_2_39
        rw [Real.log_pow] at h
        push_cast at h
        linarith [log_two_lt_frac]
      exact ⟨250, 2704 / 100, Or.inl ⟨rfl, rfl⟩, hsqrt_250, hlog39⟩
    · have hn3001 : 3001 ≤ n := by omega
      have hn3001R : (3001 : ℝ) ≤ n := by exact_mod_cast hn3001
      have hX_sq := poolMaximum_gt_1712_sq_ge_3001 sharp hn3001
      have hlin : (310 : ℝ) ^ 2 * ((519 / 1000 : ℝ) * n + 23 / 50) ≤ X := by
        change (1712 / 100 : ℝ) * (n : ℝ) ^ 2 < X at hX_sq
        nlinarith
      have hsq : y + D ≤ (X / 310) ^ 2 := by
        have hm := mul_le_mul_of_nonneg_right hlin hXpos.le
        nlinarith
      have hsqrt_310 : Real.sqrt (y + D) ≤ X / 310 := by
        calc
          Real.sqrt (y + D) ≤ Real.sqrt ((X / 310) ^ 2) := Real.sqrt_le_sqrt hsq
          _ = X / 310 := Real.sqrt_sq (by positivity)
      have hlog44 : Real.log (y + D) ≤ 61 / 2 := by
        have h := Real.log_le_log hyD_pos hyD_2_44
        rw [Real.log_pow] at h
        push_cast at h
        linarith [log_two_lt_frac]
      exact ⟨310, 61 / 2, Or.inr ⟨rfl, rfl⟩, hsqrt_310, hlog44⟩
  obtain ⟨S_denom, L_hi, hcases, hsqrt_env, hlog_env⟩ := henv

  -- Favorable-gap seed pair (r0, r0 + h) in [y - D/2, y + D/2]
  let a_s : ℝ := y - (49 / 100 : ℝ) * D
  let b_s : ℝ := y + (49 / 100 : ℝ) * D
  have hab_s : a_s ≤ b_s := by dsimp [a_s, b_s, D]; linarith
  have hb_le_yD : b_s ≤ y + D := by dsimp [b_s, D]; linarith
  let S := apInterval a_s b_s 2 1
  have hdense : b_s - a_s + 44 < 35 * (S.card : ℝ) := by
    have hta := abs_le.mp (bmor_theta_two_via_four bmor a_s (by dsimp [a_s, D]; linarith)
      (hab_s.trans (hb_le_yD.trans (hyD_1e13.trans (by norm_num)))))
    have htb := abs_le.mp (bmor_theta_two_via_four bmor b_s (by dsimp [b_s, D]; linarith)
      (hb_le_yD.trans (hyD_1e13.trans (by norm_num))))
    have hsqrt_a : Real.sqrt a_s ≤ Real.sqrt (y + D) := Real.sqrt_le_sqrt (hab_s.trans hb_le_yD)
    have hsqrt_b : Real.sqrt b_s ≤ Real.sqrt (y + D) := Real.sqrt_le_sqrt hb_le_yD
    have hinc_lo : (4508 / 10000 : ℝ) * X - (1036 / 125 : ℝ) * (X / S_denom) ≤
        thetaAP b_s 2 1 - thetaAP a_s 2 1 := by
      have hba : b_s - a_s = (4508 / 10000 : ℝ) * X := by dsimp [a_s, b_s, D]; ring
      linarith [hta.2, htb.1, hsqrt_a.trans hsqrt_env, hsqrt_b.trans hsqrt_env]
    have hlog_b : Real.log b_s ≤ L_hi :=
      (Real.log_le_log (by dsimp [b_s, D]; linarith) hb_le_yD).trans hlog_env
    have hinc_hi : thetaAP b_s 2 1 - thetaAP a_s 2 1 ≤ (S.card : ℝ) * L_hi :=
      (thetaAP_sub_le_card_mul_log_local a_s b_s 2 1 (by dsimp [a_s, D]; linarith) hab_s).trans
        (mul_le_mul_of_nonneg_left hlog_b (Nat.cast_nonneg _))
    have hba : b_s - a_s = (4508 / 10000 : ℝ) * X := by dsimp [a_s, b_s, D]; ring
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
  have hS_prime : ∀ p ∈ S, 5 < p ∧ Nat.Prime p := by
    intro p hp
    have ⟨hp_prime, ha_lt, _, _⟩ :=
      (mem_apInterval_iff a_s b_s 2 1 (by dsimp [a_s, D]; linarith) (by dsimp [b_s, D]; linarith) p).mp hp
    have hp5 : (5 : ℝ) < (p : ℝ) := by dsimp [a_s, D] at ha_lt; linarith
    exact ⟨by exact_mod_cast hp5, hp_prime⟩
  have hS_int : ∀ p ∈ S, a_s ≤ (p : ℝ) ∧ (p : ℝ) ≤ b_s := by
    intro p hp
    have ⟨_, ha_lt, hb_le, _⟩ :=
      (mem_apInterval_iff a_s b_s 2 1 (by dsimp [a_s, D]; linarith) (by dsimp [b_s, D]; linarith) p).mp hp
    exact ⟨le_of_lt ha_lt, hb_le⟩
  obtain ⟨r0, hr0_mem, h, hh, hr0h_mem⟩ :=
    exists_favorable_gap_pair_in_finset S a_s b_s hS_prime hS_int hab_s hdense
  have hr0_lo : y - D / 2 ≤ (r0 : ℝ) := by
    have := (hS_int r0 hr0_mem).1; dsimp [a_s] at this; linarith
  have hr0_hi : ((r0 + h : ℕ) : ℝ) ≤ y + D / 2 := by
    have := (hS_int (r0 + h) hr0h_mem).2; dsimp [b_s] at this; linarith
  have hh_basic := favorable_gap_basic_props h hh
  have hh_2 : 2 ≤ h := hh_basic.1
  have hh_42 : h ≤ 42 := hh_basic.2.1

  -- Half-window positivity and unit brackets / wide pair
  have hpos_half : ∀ r : ℕ, r < h → Nat.Coprime r h →
      ∀ u v : ℝ, y - D ≤ u → v ≤ y + D → D / 2 ≤ v - u →
      0 < thetaAP v h (r : ℤ) - thetaAP u h (r : ℤ) := by
    intro r hr hcop u v hu hv hw
    have hinc := bmor_finite_theta_increment_lower bmor hh hr hcop (u := u) (v := v)
      (by linarith) (by linarith) (hv.trans hyD_1e13)
    have hsqrt_v : Real.sqrt v ≤ X / 250 := (Real.sqrt_le_sqrt hv).trans hsqrt_250
    have hpos_mul : 0 < (Nat.totient h : ℝ) * (thetaAP v h (r : ℤ) - thetaAP u h (r : ℤ)) := by
      dsimp [D] at hw; linarith
    exact pos_of_mul_pos_right hpos_mul (Nat.cast_nonneg _)
  have hsupply : ∀ r : ℕ, r < h → Nat.Coprime r h →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p % h = r ∧ q % h = r ∧
        y - D ≤ (p : ℝ) ∧ (p : ℝ) ≤ y ∧ y ≤ (q : ℝ) ∧ (q : ℝ) ≤ y + D := by
    apply t75_unit_brackets_of_theta_increments h y D (by dsimp [D]; linarith) (by linarith)
    intro r hr hcop
    exact ⟨hpos_half r hr hcop (y - D) y (le_refl _) (by dsimp [D]; linarith) (by linarith),
           hpos_half r hr hcop y (y + D) (by dsimp [D]; linarith) (le_refl _) (by linarith)⟩
  have h1_lt : 1 < h := by omega
  have h1_cop : Nat.Coprime 1 h := Nat.coprime_one_left h
  obtain ⟨uw, huw_prime, huw_lo, huw_hi, huw_mod⟩ :=
    t75_prime_of_theta_increment_pos (y - D) (y - D / 2) h 1 (by linarith) (by dsimp [D]; linarith)
      (hpos_half 1 h1_lt h1_cop (y - D) (y - D / 2) (le_refl _) (by dsimp [D]; linarith) (by linarith))
  obtain ⟨vw, hvw_prime, hvw_lo, hvw_hi, hvw_mod⟩ :=
    t75_prime_of_theta_increment_pos (y + D / 2) (y + D) h 1 (by linarith) (by dsimp [D]; linarith)
      (hpos_half 1 h1_lt h1_cop (y + D / 2) (y + D) (by dsimp [D]; linarith) (le_refl _) (by linarith))
  have huw_mod' : uw % h = 1 := by
    have heq : uw % h = 1 % h := by exact_mod_cast huw_mod
    simpa [Nat.mod_eq_of_lt h1_lt] using heq
  have hvw_mod' : vw % h = 1 := by
    have heq : vw % h = 1 % h := by exact_mod_cast hvw_mod
    simpa [Nat.mod_eq_of_lt h1_lt] using heq

  -- Central prime Finset A = apInterval (y - D/2) (y + D/2) h 1
  let A := apInterval (y - D / 2) (y + D / 2) h 1
  have hA_prime : ∀ p ∈ A, Nat.Prime p := by
    intro p hp
    exact ((mem_apInterval_iff (y - D / 2) (y + D / 2) h 1 (by linarith) (by linarith) p).mp hp).1
  have hA_int : ∀ p ∈ A, y - D / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ y + D / 2 := by
    intro p hp
    have ⟨_, hlo, hhi, _⟩ := (mem_apInterval_iff (y - D / 2) (y + D / 2) h 1 (by linarith) (by linarith) p).mp hp
    exact ⟨le_of_lt hlo, hhi⟩
  have hA_mod : ∀ p ∈ A, p % h = 1 := by
    intro p hp
    have ⟨_, _, _, hmod⟩ := (mem_apInterval_iff (y - D / 2) (y + D / 2) h 1 (by linarith) (by linarith) p).mp hp
    have heq : p % h = 1 % h := by exact_mod_cast hmod
    simpa [Nat.mod_eq_of_lt h1_lt] using heq
  have hA_inc_lo := bmor_finite_theta_increment_lower bmor hh h1_lt h1_cop
    (u := y - D / 2) (v := y + D / 2) (by dsimp [D]; linarith) (by dsimp [D]; linarith)
    ((by dsimp [D]; linarith : y + D / 2 ≤ y + D).trans hyD_1e13)
  have hsqrt_mid : Real.sqrt (y + D / 2) ≤ X / S_denom :=
    (Real.sqrt_le_sqrt (by dsimp [D]; linarith : y + D / 2 ≤ y + D)).trans hsqrt_env
  have hlog_mid : Real.log (y + D / 2) ≤ L_hi :=
    (Real.log_le_log (by dsimp [D]; linarith) (by dsimp [D]; linarith : y + D / 2 ≤ y + D)).trans hlog_env
  have hA_inc_hi : thetaAP (y + D / 2) h 1 - thetaAP (y - D / 2) h 1 ≤ (A.card : ℝ) * L_hi :=
    (thetaAP_sub_le_card_mul_log_local (y - D / 2) (y + D / 2) h 1 (by dsimp [D]; linarith) (by dsimp [D]; linarith)).trans
      (mul_le_mul_of_nonneg_left hlog_mid (Nat.cast_nonneg _))
  have hphi_2 : 2 * (Nat.totient h : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_basic.2.2
  have hphi_pos : (0 : ℝ) ≤ (Nat.totient h : ℝ) := Nat.cast_nonneg _
  have hphi_card : (Nat.totient h : ℝ) * (thetaAP (y + D / 2) h 1 - thetaAP (y - D / 2) h 1) ≤
      (L_hi / 2) * (h : ℝ) * (A.card : ℝ) := by
    have hm1 := mul_le_mul_of_nonneg_left hA_inc_hi hphi_pos
    have hm2 := mul_le_mul_of_nonneg_right hphi_2 (Nat.cast_nonneg A.card)
    rcases hcases with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> nlinarith
  have hA_card : D < 24 * (h : ℝ) * (A.card : ℝ) := by
    have hw_eq : (y + D / 2) - (y - D / 2) = D := by ring
    dsimp [D] at hw_eq hA_inc_lo ⊢
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
  have hD_lo : 3072 * (h : ℝ) ≤ D := by
    have hh_hi : (h : ℝ) ≤ 42 := by exact_mod_cast hh_42
    dsimp [D]
    linarith
  have hA_card_ge : 2 ≤ A.card := by
    have hh_hi : (h : ℝ) ≤ 42 := by exact_mod_cast hh_42
    have hcard_real : (2 : ℝ) ≤ (A.card : ℝ) := by nlinarith
    exact_mod_cast hcard_real

  -- Apply compact binning with k1 = 170 (n ≤ 2299) or k1 = 220 (2300 ≤ n ≤ 9299)
  have hh_lo_real : (2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_2
  by_cases h2299 : n ≤ 2299
  · have hX2299 := poolMaximum_upper_le_2299 upperSharp hnlo h2299
    have hD_upper : D * (65 : ℝ) ^ 170 < (16 * 104 : ℝ) * (h : ℝ) * (69 : ℝ) ^ 170 := by
      have h1 : D < (23 / 50 : ℝ) * ((5285402 : ℝ) * (1828 / 100 : ℝ)) := by dsimp [D]; linarith
      have hnat : 23 * 5285402 * 1828 * 65 ^ 170 < 50 * 100 * 3328 * 69 ^ 170 := by decide
      have hnatR : ((23 * 5285402 * 1828 * 65 ^ 170 : ℕ) : ℝ) <
          ((50 * 100 * 3328 * 69 ^ 170 : ℕ) : ℝ) := Nat.cast_lt.mpr hnat
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hnatR
      have h2 : ((23 / 50 : ℝ) * ((5285402 : ℝ) * (1828 / 100 : ℝ))) * (65 : ℝ) ^ 170 <
          (16 * 104 : ℝ) * 2 * (69 : ℝ) ^ 170 := by
        have hmul := div_lt_div_of_pos_right hnatR (by norm_num : (0 : ℝ) < 50 * 100)
        calc
          ((23 / 50 : ℝ) * ((5285402 : ℝ) * (1828 / 100 : ℝ))) * (65 : ℝ) ^ 170
            = (23 * 5285402 * 1828 * (65 : ℝ) ^ 170) / (50 * 100) := by ring
          _ < (50 * 100 * 3328 * (69 : ℝ) ^ 170) / (50 * 100) := hmul
          _ = (16 * 104 : ℝ) * 2 * (69 : ℝ) ^ 170 := by ring
      have h3 := mul_lt_mul_of_pos_right h1 (by positivity : (0 : ℝ) < (65 : ℝ) ^ 170)
      have h4 : (16 * 104 : ℝ) * 2 * (69 : ℝ) ^ 170 ≤ (16 * 104 : ℝ) * (h : ℝ) * (69 : ℝ) ^ 170 := by
        have hm := mul_le_mul_of_nonneg_left hh_lo_real (by norm_num : (0 : ℝ) ≤ 16 * 104)
        exact mul_le_mul_of_nonneg_right hm (by positivity)
      exact lt_of_lt_of_le (lt_trans h3 h2) h4
    exact t75_compact_targets_from_supplies (by omega) hn (k1 := 170) (by omega) hh
      y D rfl hyD_gt_two hD_lo hD_upper hsupply
      r0 (hS_prime r0 hr0_mem).2 (hS_prime (r0 + h) hr0h_mem).2 hr0_lo hr0_hi
      A hA_prime hA_int hA_mod hA_card_ge hA_card
      uw vw huw_prime hvw_prime huw_mod' hvw_mod' ⟨le_of_lt huw_lo, huw_hi⟩ ⟨le_of_lt hvw_lo, hvw_hi⟩
  · have hn2301 : 2301 ≤ n := by
      obtain ⟨k, hk⟩ := hn
      omega
    have hD_upper : D * (65 : ℝ) ^ 220 < (16 * 104 : ℝ) * (h : ℝ) * (69 : ℝ) ^ 220 := by
      have h1 : D < (23 / 50 : ℝ) * ((86471402 : ℝ) * (2162 / 100 : ℝ)) := by dsimp [D]; linarith
      have hnat : 23 * 86471402 * 2162 * 65 ^ 220 < 50 * 100 * 3328 * 69 ^ 220 := by decide
      have hnatR : ((23 * 86471402 * 2162 * 65 ^ 220 : ℕ) : ℝ) <
          ((50 * 100 * 3328 * 69 ^ 220 : ℕ) : ℝ) := Nat.cast_lt.mpr hnat
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hnatR
      have h2 : ((23 / 50 : ℝ) * ((86471402 : ℝ) * (2162 / 100 : ℝ))) * (65 : ℝ) ^ 220 <
          (16 * 104 : ℝ) * 2 * (69 : ℝ) ^ 220 := by
        have hmul := div_lt_div_of_pos_right hnatR (by norm_num : (0 : ℝ) < 50 * 100)
        calc
          ((23 / 50 : ℝ) * ((86471402 : ℝ) * (2162 / 100 : ℝ))) * (65 : ℝ) ^ 220
            = (23 * 86471402 * 2162 * (65 : ℝ) ^ 220) / (50 * 100) := by ring
          _ < (50 * 100 * 3328 * (69 : ℝ) ^ 220) / (50 * 100) := hmul
          _ = (16 * 104 : ℝ) * 2 * (69 : ℝ) ^ 220 := by ring
      have h3 := mul_lt_mul_of_pos_right h1 (by positivity : (0 : ℝ) < (65 : ℝ) ^ 220)
      have h4 : (16 * 104 : ℝ) * 2 * (69 : ℝ) ^ 220 ≤ (16 * 104 : ℝ) * (h : ℝ) * (69 : ℝ) ^ 220 := by
        have hm := mul_le_mul_of_nonneg_left hh_lo_real (by norm_num : (0 : ℝ) ≤ 16 * 104)
        exact mul_le_mul_of_nonneg_right hm (by positivity)
      exact lt_of_lt_of_le (lt_trans h3 h2) h4
    exact t75_compact_targets_from_supplies (by omega) hn (k1 := 220) (by omega) hh
      y D rfl hyD_gt_two hD_lo hD_upper hsupply
      r0 (hS_prime r0 hr0_mem).2 (hS_prime (r0 + h) hr0h_mem).2 hr0_lo hr0_hi
      A hA_prime hA_int hA_mod hA_card_ge hA_card
      uw vw huw_prime hvw_prime huw_mod' hvw_mod' ⟨le_of_lt huw_lo, huw_hi⟩ ⟨le_of_lt hvw_lo, hvw_hi⟩

/-! ### Section 5: High Regime (`9301 ≤ n ≤ 19483`, `D = y / 400`) -/

private theorem high_theta_increment_lower_ge_7e12
    (imp : BMORExplicitFormulaImports) {h r : ℕ}
    (hh : h ∈ t75FavorableGaps) (hr : r < h) (hcop : Nat.Coprime r h)
    {u v : ℝ} (hu_lo : (7 * 10 ^ 12 : ℝ) ≤ u) (huv : u ≤ v) :
    (Nat.totient h : ℝ) * (thetaAP v h (r : ℤ) - thetaAP u h (r : ℤ)) ≥
      (v - u) - (u + v) / 2700 := by
  have hv_lo : (7 * 10 ^ 12 : ℝ) ≤ v := hu_lo.trans huv
  by_cases h2 : h = 2
  · subst h
    have hr1 : r = 1 := by
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · exact False.elim (absurd hcop (by decide))
      · rfl
    subst r
    have htu := abs_le.mp (bmor_theta_mod_two_all_ge_7e12 imp hu_lo)
    have htv := abs_le.mp (bmor_theta_mod_two_all_ge_7e12 imp hv_lo)
    have htot2 : (Nat.totient 2 : ℝ) = 1 := by norm_num
    rw [htot2]
    push_cast
    linarith
  · obtain ⟨q, hq_def, hq3, hq36, hphi12, hphi_eq, hcop_q⟩ :=
      favorable_gap_reduced_modulus hh h2 hr hcop
    have htu := abs_le.mp (bmor_theta_small_moduli_signed_ge_7e12 imp hq3 hq36 hphi12 hcop_q hu_lo)
    have htv := abs_le.mp (bmor_theta_small_moduli_signed_ge_7e12 imp hq3 hq36 hphi12 hcop_q hv_lo)
    have hinc_eq : thetaAP v h (r : ℤ) - thetaAP u h (r : ℤ) =
        thetaAP v q ((r % q : ℕ) : ℤ) - thetaAP u q ((r % q : ℕ) : ℤ) := by
      by_cases h42 : h = 42
      · subst h
        rw [hq_def, if_pos rfl]
        exact thetaAP_forty_two_increment_eq_twenty_one (by linarith) huv hr hcop
      · rw [hq_def, if_neg h42, Nat.mod_eq_of_lt hr]
    rw [hinc_eq, hphi_eq]
    linarith

/-- T75 prime target vector across `9301 ≤ n ≤ 19483, Odd n` with `D = y / 400`. -/
theorem fc2k_t75_targets_high
    (imp : BMORExplicitFormulaImports) (rs : RSPrimeCountImports)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 9301 ≤ n) (hnhi : n ≤ 19483) (hn : Odd n) :
    let y : ℝ := (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let D : ℝ := y / 400
    ∃ f : Fin n → ℕ,
      (∑ i, f i) = Lucas.poolTotal n ∧
      (∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ) - y| ≤ D) := by
  dsimp only
  let X : ℝ := poolMaximum n
  let y : ℝ := (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue
  let D : ℝ := y / 400
  have hX_lo : (86508602 : ℝ) * (1954 / 100 : ℝ) < X := poolMaximum_gt_ge_9301 sharp hnlo
  have hX_hi : X < (379587290 : ℝ) * (2362 / 100 : ℝ) := poolMaximum_upper_le_19483 upperSharp hnlo hnhi
  have hXpos : 0 < X := by linarith
  have hm_bounds := global_pool_mean_bounds rs sharp (by omega : 2001 ≤ n)
  have hm_lo : (449 / 1000 : ℝ) * X < centralEntriesMean (prescribedPoolValues n) centralPoolValue := by
    rw [prescribedPoolValues_mean]
    exact (lt_div_iff₀ hXpos).mp hm_bounds.1
  have hm_hi : centralEntriesMean (prescribedPoolValues n) centralPoolValue < (519 / 1000 : ℝ) * X := by
    rw [prescribedPoolValues_mean]
    exact (div_lt_iff₀ hXpos).mp hm_bounds.2
  have hnloR : (9301 : ℝ) ≤ n := by exact_mod_cast hnlo
  have hnhiR : (n : ℝ) ≤ 19483 := by exact_mod_cast hnhi
  have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hy_lo : 9301 * ((449 / 1000 : ℝ) * ((86508602 : ℝ) * (1954 / 100 : ℝ))) ≤ y := by
    have hm1 : (449 / 1000 : ℝ) * ((86508602 : ℝ) * (1954 / 100 : ℝ)) ≤
        centralEntriesMean (prescribedPoolValues n) centralPoolValue := by linarith
    dsimp [y]
    exact mul_le_mul hnloR hm1 (by positivity) hn_nonneg
  have hy_hi : y ≤ 19483 * ((519 / 1000 : ℝ) * ((379587290 : ℝ) * (2362 / 100 : ℝ))) := by
    have hm1 : centralEntriesMean (prescribedPoolValues n) centralPoolValue ≤
        (519 / 1000 : ℝ) * ((379587290 : ℝ) * (2362 / 100 : ℝ)) := by linarith
    have hy1 : y ≤ (n : ℝ) * ((519 / 1000 : ℝ) * ((379587290 : ℝ) * (2362 / 100 : ℝ))) := by
      dsimp [y]
      exact mul_le_mul_of_nonneg_left hm1 hn_nonneg
    linarith
  have hy_eq : y = 400 * D := by dsimp [D]; ring
  have hyD_7e12 : (7 * 10 ^ 12 : ℝ) < y - D := by dsimp [D]; linarith
  have hD_1e10 : (17 * 10 ^ 9 : ℝ) < D := by dsimp [D]; linarith
  have hyD_2_47 : y + D ≤ (2 : ℝ) ^ 47 := by dsimp [D]; linarith
  have hlog_47 : Real.log (y + D) ≤ 3258 / 100 := by
    have h := Real.log_le_log (by linarith) hyD_2_47
    rw [Real.log_pow] at h
    push_cast at h
    linarith [log_two_lt_frac]

  -- Seed pair (r0, r0 + h) in [y - D/2, y + D/2]
  let a_s : ℝ := y - (49 / 100 : ℝ) * D
  let b_s : ℝ := y + (49 / 100 : ℝ) * D
  have ha_lo : (7 * 10 ^ 12 : ℝ) ≤ a_s := by dsimp [a_s]; linarith
  have hab_s : a_s ≤ b_s := by dsimp [a_s, b_s]; linarith
  have hb_le_yD : b_s ≤ y + D := by dsimp [b_s]; linarith
  let S := apInterval a_s b_s 2 1
  have hdense : b_s - a_s + 44 < 35 * (S.card : ℝ) := by
    have hta := abs_le.mp (bmor_theta_mod_two_all_ge_7e12 imp ha_lo)
    have htb := abs_le.mp (bmor_theta_mod_two_all_ge_7e12 imp (ha_lo.trans hab_s))
    have hinc_lo : (284 / 300 : ℝ) * D ≤ thetaAP b_s 2 1 - thetaAP a_s 2 1 := by
      have hba : b_s - a_s - (a_s + b_s) / 24000 = (284 / 300 : ℝ) * D := by
        dsimp [a_s, b_s]; rw [hy_eq]; ring
      linarith [hta.2, htb.1]
    have hlog_b : Real.log b_s ≤ 3258 / 100 :=
      (Real.log_le_log (by linarith) hb_le_yD).trans hlog_47
    have hinc_hi : thetaAP b_s 2 1 - thetaAP a_s 2 1 ≤ (S.card : ℝ) * (3258 / 100 : ℝ) :=
      (thetaAP_sub_le_card_mul_log_local a_s b_s 2 1 (by linarith) hab_s).trans
        (mul_le_mul_of_nonneg_left hlog_b (Nat.cast_nonneg _))
    have hba : b_s - a_s = (98 / 100 : ℝ) * D := by dsimp [a_s, b_s]; ring
    linarith
  have hS_prime : ∀ p ∈ S, 5 < p ∧ Nat.Prime p := by
    intro p hp
    have ⟨hp_prime, ha_lt, _, _⟩ :=
      (mem_apInterval_iff a_s b_s 2 1 (by linarith) (by linarith) p).mp hp
    have hp5 : (5 : ℝ) < (p : ℝ) := by linarith
    exact ⟨by exact_mod_cast hp5, hp_prime⟩
  have hS_int : ∀ p ∈ S, a_s ≤ (p : ℝ) ∧ (p : ℝ) ≤ b_s := by
    intro p hp
    have ⟨_, ha_lt, hb_le, _⟩ :=
      (mem_apInterval_iff a_s b_s 2 1 (by linarith) (by linarith) p).mp hp
    exact ⟨le_of_lt ha_lt, hb_le⟩
  obtain ⟨r0, hr0_mem, h, hh, hr0h_mem⟩ :=
    exists_favorable_gap_pair_in_finset S a_s b_s hS_prime hS_int hab_s hdense
  have hr0_lo : y - D / 2 ≤ (r0 : ℝ) := by
    have := (hS_int r0 hr0_mem).1; dsimp [a_s] at this; linarith
  have hr0_hi : ((r0 + h : ℕ) : ℝ) ≤ y + D / 2 := by
    have := (hS_int (r0 + h) hr0h_mem).2; dsimp [b_s] at this; linarith
  have hh_basic := favorable_gap_basic_props h hh
  have hh_2 : 2 ≤ h := hh_basic.1
  have hh_42 : h ≤ 42 := hh_basic.2.1

  -- Half-window positivity and unit brackets / wide pair
  have hpos_half : ∀ r : ℕ, r < h → Nat.Coprime r h →
      ∀ u v : ℝ, y - D ≤ u → v ≤ y + D → D / 2 ≤ v - u →
      0 < thetaAP v h (r : ℤ) - thetaAP u h (r : ℤ) := by
    intro r hr hcop u v hu hv hw
    have hinc := high_theta_increment_lower_ge_7e12 imp hh hr hcop (u := u) (v := v)
      (hyD_7e12.le.trans hu) (by linarith)
    have hpos_mul : 0 < (Nat.totient h : ℝ) * (thetaAP v h (r : ℤ) - thetaAP u h (r : ℤ)) := by
      linarith
    exact pos_of_mul_pos_right hpos_mul (Nat.cast_nonneg _)
  have hsupply : ∀ r : ℕ, r < h → Nat.Coprime r h →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p % h = r ∧ q % h = r ∧
        y - D ≤ (p : ℝ) ∧ (p : ℝ) ≤ y ∧ y ≤ (q : ℝ) ∧ (q : ℝ) ≤ y + D := by
    apply t75_unit_brackets_of_theta_increments h y D (by linarith) (by linarith)
    intro r hr hcop
    exact ⟨hpos_half r hr hcop (y - D) y (le_refl _) (by linarith) (by linarith),
           hpos_half r hr hcop y (y + D) (by linarith) (le_refl _) (by linarith)⟩
  have h1_lt : 1 < h := by omega
  have h1_cop : Nat.Coprime 1 h := Nat.coprime_one_left h
  obtain ⟨uw, huw_prime, huw_lo, huw_hi, huw_mod⟩ :=
    t75_prime_of_theta_increment_pos (y - D) (y - D / 2) h 1 (by linarith) (by linarith)
      (hpos_half 1 h1_lt h1_cop (y - D) (y - D / 2) (le_refl _) (by linarith) (by linarith))
  obtain ⟨vw, hvw_prime, hvw_lo, hvw_hi, hvw_mod⟩ :=
    t75_prime_of_theta_increment_pos (y + D / 2) (y + D) h 1 (by linarith) (by linarith)
      (hpos_half 1 h1_lt h1_cop (y + D / 2) (y + D) (by linarith) (le_refl _) (by linarith))
  have huw_mod' : uw % h = 1 := by
    have heq : uw % h = 1 % h := by exact_mod_cast huw_mod
    simpa [Nat.mod_eq_of_lt h1_lt] using heq
  have hvw_mod' : vw % h = 1 := by
    have heq : vw % h = 1 % h := by exact_mod_cast hvw_mod
    simpa [Nat.mod_eq_of_lt h1_lt] using heq

  -- Central prime Finset A = apInterval (y - D/2) (y + D/2) h 1
  let A := apInterval (y - D / 2) (y + D / 2) h 1
  have hA_prime : ∀ p ∈ A, Nat.Prime p := by
    intro p hp
    exact ((mem_apInterval_iff (y - D / 2) (y + D / 2) h 1 (by linarith) (by linarith) p).mp hp).1
  have hA_int : ∀ p ∈ A, y - D / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ y + D / 2 := by
    intro p hp
    have ⟨_, hlo, hhi, _⟩ := (mem_apInterval_iff (y - D / 2) (y + D / 2) h 1 (by linarith) (by linarith) p).mp hp
    exact ⟨le_of_lt hlo, hhi⟩
  have hA_mod : ∀ p ∈ A, p % h = 1 := by
    intro p hp
    have ⟨_, _, _, hmod⟩ := (mem_apInterval_iff (y - D / 2) (y + D / 2) h 1 (by linarith) (by linarith) p).mp hp
    have heq : p % h = 1 % h := by exact_mod_cast hmod
    simpa [Nat.mod_eq_of_lt h1_lt] using heq
  have hA_inc_lo := high_theta_increment_lower_ge_7e12 imp hh h1_lt h1_cop
    (u := y - D / 2) (v := y + D / 2) (by linarith) (by linarith)
  have hlog_mid : Real.log (y + D / 2) ≤ 3258 / 100 :=
    (Real.log_le_log (by linarith) (by linarith : y + D / 2 ≤ y + D)).trans hlog_47
  have hA_inc_hi : thetaAP (y + D / 2) h 1 - thetaAP (y - D / 2) h 1 ≤ (A.card : ℝ) * (3258 / 100 : ℝ) :=
    (thetaAP_sub_le_card_mul_log_local (y - D / 2) (y + D / 2) h 1 (by linarith) (by linarith)).trans
      (mul_le_mul_of_nonneg_left hlog_mid (Nat.cast_nonneg _))
  have hphi_2 : 2 * (Nat.totient h : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_basic.2.2
  have hphi_pos : (0 : ℝ) ≤ (Nat.totient h : ℝ) := Nat.cast_nonneg _
  have hphi_card : (Nat.totient h : ℝ) * (thetaAP (y + D / 2) h 1 - thetaAP (y - D / 2) h 1) ≤
      (1629 / 100 : ℝ) * (h : ℝ) * (A.card : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hA_inc_hi hphi_pos,
               mul_le_mul_of_nonneg_right hphi_2 (Nat.cast_nonneg A.card)]
  have hA_card : D < 24 * (h : ℝ) * (A.card : ℝ) := by linarith
  have hh_hi : (h : ℝ) ≤ 42 := by exact_mod_cast hh_42
  have hh_lo_real : (2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_2
  have hD_lo : 3072 * (h : ℝ) ≤ D := by linarith
  have hA_card_ge : 2 ≤ A.card := by
    have hcard_real : (2 : ℝ) ≤ (A.card : ℝ) := by nlinarith
    exact_mod_cast hcard_real
  have hD_upper : D * (65 : ℝ) ^ 315 < (16 * 104 : ℝ) * (h : ℝ) * (69 : ℝ) ^ 315 := by
    have h1 : D ≤ (19483 * ((519 / 1000 : ℝ) * ((379587290 : ℝ) * (2362 / 100 : ℝ)))) / 400 := by
      dsimp [D]; linarith
    have hnat : 19483 * 519 * 379587290 * 2362 * 65 ^ 315 < 400 * 1000 * 100 * 3328 * 69 ^ 315 := by decide
    have hnatR : ((19483 * 519 * 379587290 * 2362 * 65 ^ 315 : ℕ) : ℝ) <
        ((400 * 1000 * 100 * 3328 * 69 ^ 315 : ℕ) : ℝ) := Nat.cast_lt.mpr hnat
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hnatR
    have h2 : ((19483 * ((519 / 1000 : ℝ) * ((379587290 : ℝ) * (2362 / 100 : ℝ)))) / 400) * (65 : ℝ) ^ 315 <
        (16 * 104 : ℝ) * 2 * (69 : ℝ) ^ 315 := by
      have hmul := div_lt_div_of_pos_right hnatR (by norm_num : (0 : ℝ) < 400 * 1000 * 100)
      calc
        ((19483 * ((519 / 1000 : ℝ) * ((379587290 : ℝ) * (2362 / 100 : ℝ)))) / 400) * (65 : ℝ) ^ 315
          = (19483 * 519 * 379587290 * 2362 * (65 : ℝ) ^ 315) / (400 * 1000 * 100) := by ring
        _ < (400 * 1000 * 100 * 3328 * (69 : ℝ) ^ 315) / (400 * 1000 * 100) := hmul
        _ = (16 * 104 : ℝ) * 2 * (69 : ℝ) ^ 315 := by ring
    have h3 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ (65 : ℝ) ^ 315)
    have h4 : (16 * 104 : ℝ) * 2 * (69 : ℝ) ^ 315 ≤ (16 * 104 : ℝ) * (h : ℝ) * (69 : ℝ) ^ 315 := by
      have hm := mul_le_mul_of_nonneg_left hh_lo_real (by norm_num : (0 : ℝ) ≤ 16 * 104)
      exact mul_le_mul_of_nonneg_right hm (by positivity)
    exact lt_of_le_of_lt h3 (lt_of_lt_of_le h2 h4)
  exact t75_compact_targets_from_supplies (by omega) hn (k1 := 315) (by omega) hh
    y D rfl (by linarith) hD_lo hD_upper hsupply
    r0 (hS_prime r0 hr0_mem).2 (hS_prime (r0 + h) hr0h_mem).2 hr0_lo hr0_hi
    A hA_prime hA_int hA_mod hA_card_ge hA_card
    uw vw huw_prime hvw_prime huw_mod' hvw_mod' ⟨le_of_lt huw_lo, huw_hi⟩ ⟨le_of_lt hvw_lo, hvw_hi⟩

end

end Sude
