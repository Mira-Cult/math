import Sude.BMORExplicitFormulaImports
import Sude.T75WheelPotential
import Sude.T75ThetaIntervalBrackets
import Sude.FWT75NominalSupplyTargets
import Sude.FWFirstBandReachableDiagonalRepair
import Sude.FWUpperBandsCrossing

/-!
# First-Band T75 and Diagonal Prime Supplies from BMOR Explicit-Formula Imports

From `BMORExplicitFormulaImports`, `BMORFiniteTheta`, and `RSIndexImports`, this module proves:
1. Uniform parity theta enclosure `|thetaAP x 2 1 - x| ≤ x / 50000` for `4 * 10^13 ≤ x` and `log x ≤ 34`.
2. Uniform small-moduli theta enclosure `φ(q) * |thetaAP x q a - x / φ(q)| ≤ x / 5000`
   for `3 ≤ q ≤ 36`, `φ(q) ≤ 12`, `gcd(q, a) = 1`, `4 * 10^13 ≤ x`, and `log x ≤ 34`.
3. Favorable-gap seed pair `(r0, r0 + h)` in `[y - D/2, y + D/2]` via `exists_favorable_gap_pair_in_finset`.
4. Central prime set `A`, wide prime pair `(uw, vw)`, unit-bracket supply `hsupply`, and
   reachable diagonal odd prime supply `hdiagPrime`.
5. First-band `HasSquare n` for `19485 ≤ n ≤ 21248, Odd n` given only the seed twin-prime supply.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

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
  have hlog2 := log_two_gt_frac
  push_cast at hlog4
  linarith

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
  have hquad2 : (lam - c) + (lam - c) ^ 2 / 2 ≤ 23 + 23 ^ 2 / 2 := by
    nlinarith
  have hnum : (ν - c) + (lam - c) + ((lam - c) ^ 2 - (ν - c) ^ 2) / 2 ≤ 288 := by
    linarith
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

/-- Uniform parity theta enclosure for `x ≥ 4 * 10^13` with `log x ≤ 36`:
    `|thetaAP x 2 1 - x| ≤ x / 50000`. -/
theorem bmor_theta_mod_two_uniform
    (imp : BMORExplicitFormulaImports)
    {x : ℝ} (hx : (4 * 10 ^ 13 : ℝ) ≤ x) (hlog_hi : Real.log x ≤ 36) :
    |thetaAP x 2 1 - x| ≤ x / 50000 := by
  have hlog_lo : (28 : ℝ) ≤ Real.log x := by
    have h2_45 : (2 : ℝ) ^ 45 ≤ x := by linarith [show (2 : ℝ) ^ 45 ≤ 4 * 10 ^ 13 by norm_num]
    have h := Real.log_le_log (by positivity) h2_45
    rw [Real.log_pow] at h
    push_cast at h
    linarith [log_two_gt_frac]
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
  have hsqrt : Real.sqrt x ≤ x / 6324555 := by
    have hsq : (6324555 : ℝ) ^ 2 ≤ x := by linarith [show (6324555 : ℝ) ^ 2 ≤ 4 * 10 ^ 13 by norm_num]
    have hle : (6324555 : ℝ) ≤ Real.sqrt x := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 6324555)]
      exact Real.sqrt_le_sqrt hsq
    have hmul : (6324555 : ℝ) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
      mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg x)
    rw [Real.mul_self_sqrt (by linarith)] at hmul
    linarith
  have hmain : ((10 : ℝ) * (2 / 10 ^ 7 : ℝ) / 2 +
      bmorSmoothFactor 10 (2 / 10 ^ 7 : ℝ) * bmorParityHighZeroSum (3 * 10 ^ 10 : ℝ) 10) * x ≤
      (1 / 10 ^ 6 + 1 / 10 ^ 10) * x := by
    nlinarith
  norm_num at hpt
  linarith

private theorem bmor_theta_mod_two_bandA
    (imp : BMORExplicitFormulaImports)
    {x : ℝ} (hx : (88 * 10 ^ 12 : ℝ) ≤ x) (hlog_hi : Real.log x ≤ 36) :
    |thetaAP x 2 1 - x| ≤ x / 80000 := by
  have hlog_lo : (28 : ℝ) ≤ Real.log x := by
    have h2_45 : (2 : ℝ) ^ 45 ≤ x := by linarith [show (2 : ℝ) ^ 45 ≤ 88 * 10 ^ 12 by norm_num]
    have h := Real.log_le_log (by positivity) h2_45
    rw [Real.log_pow] at h
    push_cast at h
    linarith [log_two_gt_frac]
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
  have hsqrt : Real.sqrt x ≤ x / 9380000 := by
    have hsq : (9380000 : ℝ) ^ 2 ≤ x := by linarith [show (9380000 : ℝ) ^ 2 ≤ 88 * 10 ^ 12 by norm_num]
    have hle : (9380000 : ℝ) ≤ Real.sqrt x := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 9380000)]
      exact Real.sqrt_le_sqrt hsq
    have hmul : (9380000 : ℝ) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
      mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg x)
    rw [Real.mul_self_sqrt (by linarith)] at hmul
    linarith
  have hmain : ((10 : ℝ) * (2 / 10 ^ 7 : ℝ) / 2 +
      bmorSmoothFactor 10 (2 / 10 ^ 7 : ℝ) * bmorParityHighZeroSum (3 * 10 ^ 10 : ℝ) 10) * x ≤
      (1 / 10 ^ 6 + 1 / 10 ^ 10) * x := by
    nlinarith
  norm_num at hpt
  linarith

private theorem bmor_theta_mod_two_bandB
    (imp : BMORExplicitFormulaImports)
    {x : ℝ} (hx : (200 * 10 ^ 12 : ℝ) ≤ x) (hlog_hi : Real.log x ≤ 36) :
    |thetaAP x 2 1 - x| ≤ x / 115000 := by
  have hlog_lo : (28 : ℝ) ≤ Real.log x := by
    have h2_45 : (2 : ℝ) ^ 45 ≤ x := by linarith [show (2 : ℝ) ^ 45 ≤ 200 * 10 ^ 12 by norm_num]
    have h := Real.log_le_log (by positivity) h2_45
    rw [Real.log_pow] at h
    push_cast at h
    linarith [log_two_gt_frac]
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
  have hsqrt : Real.sqrt x ≤ x / 14142000 := by
    have hsq : (14142000 : ℝ) ^ 2 ≤ x := by linarith [show (14142000 : ℝ) ^ 2 ≤ 200 * 10 ^ 12 by norm_num]
    have hle : (14142000 : ℝ) ≤ Real.sqrt x := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 14142000)]
      exact Real.sqrt_le_sqrt hsq
    have hmul : (14142000 : ℝ) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
      mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg x)
    rw [Real.mul_self_sqrt (by linarith)] at hmul
    linarith
  have hmain : ((10 : ℝ) * (2 / 10 ^ 7 : ℝ) / 2 +
      bmorSmoothFactor 10 (2 / 10 ^ 7 : ℝ) * bmorParityHighZeroSum (3 * 10 ^ 10 : ℝ) 10) * x ≤
      (1 / 10 ^ 6 + 1 / 10 ^ 10) * x := by
    nlinarith
  norm_num at hpt
  linarith

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

/-- Uniform small-moduli theta enclosure for `3 ≤ q ≤ 36`, `φ(q) ≤ 12`, `gcd(q, a) = 1`,
    and `x ≥ 4 * 10^13` with `log x ≤ 34`:
    `φ(q) * |thetaAP x q a - x / φ(q)| ≤ x / 5000`. -/
theorem bmor_theta_small_moduli_uniform
    (imp : BMORExplicitFormulaImports)
    {q : ℕ} {a : ℤ} {x : ℝ}
    (hq3 : 3 ≤ q) (hq36 : q ≤ 36) (hphi : (Nat.totient q : ℝ) ≤ 12)
    (hcop : Nat.Coprime q a.natAbs)
    (hx : (4 * 10 ^ 13 : ℝ) ≤ x) (hlog_hi : Real.log x ≤ 36) :
    (Nat.totient q : ℝ) * |thetaAP x q a - x / (Nat.totient q : ℝ)| ≤ x / 5000 := by
  have hlog_lo : (28 : ℝ) ≤ Real.log x := by
    have h2_45 : (2 : ℝ) ^ 45 ≤ x := by linarith [show (2 : ℝ) ^ 45 ≤ 4 * 10 ^ 13 by norm_num]
    have h := Real.log_le_log (by positivity) h2_45
    rw [Real.log_pow] at h
    push_cast at h
    linarith [log_two_gt_frac]
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
  have hsqrt : Real.sqrt x ≤ x / 6324555 := by
    have hsq : (6324555 : ℝ) ^ 2 ≤ x := by linarith [show (6324555 : ℝ) ^ 2 ≤ 4 * 10 ^ 13 by norm_num]
    have hle : (6324555 : ℝ) ≤ Real.sqrt x := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 6324555)]
      exact Real.sqrt_le_sqrt hsq
    have hmul : (6324555 : ℝ) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
      mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg x)
    rw [Real.mul_self_sqrt (by linarith)] at hmul
    linarith
  have hmain : ((10 : ℝ) * (1 / 10 ^ 5 : ℝ) / 2 +
      bmorSmoothFactor 10 (1 / 10 ^ 5 : ℝ) * bmorHighZeroSum (36 : ℝ) 12 28 10) * x ≤
      (5 / 10 ^ 5 + 1 / 10 ^ 9) * x := by
    nlinarith
  norm_num at hpt
  linarith

private theorem bmor_theta_small_moduli_signed
    (imp : BMORExplicitFormulaImports)
    {q : ℕ} {a : ℤ} {x : ℝ}
    (hq3 : 3 ≤ q) (hq36 : q ≤ 36) (hphi : (Nat.totient q : ℝ) ≤ 12)
    (hcop : Nat.Coprime q a.natAbs)
    (hx : (4 * 10 ^ 13 : ℝ) ≤ x) (hlog_hi : Real.log x ≤ 36) :
    |(Nat.totient q : ℝ) * thetaAP x q a - x| ≤ x / 5000 := by
  have h := bmor_theta_small_moduli_uniform imp hq3 hq36 hphi hcop hx hlog_hi
  have hphi_pos : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have heq : |(Nat.totient q : ℝ) * thetaAP x q a - x| =
      (Nat.totient q : ℝ) * |thetaAP x q a - x / (Nat.totient q : ℝ)| := by
    have h1 : (Nat.totient q : ℝ) * thetaAP x q a - x =
        (Nat.totient q : ℝ) * (thetaAP x q a - x / (Nat.totient q : ℝ)) := by
      field_simp
    rw [h1, abs_mul, abs_of_pos hphi_pos]
  rwa [← heq] at h

private theorem fw_all_bands_upper_index_ratio
    (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    (poolMaximum n : ℝ) ≤ (23601 / 1000 : ℝ) * (n : ℝ) ^ 2 := by
  have hnloR : (19485 : ℝ) ≤ n := by exact_mod_cast hnlo
  have hnhiR : (n : ℝ) ≤ 35733 := by exact_mod_cast hnhi
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hjpos : 0 < j := by dsimp [j]; positivity
  have hjone : 1 < j := by dsimp [j]; push_cast; nlinarith
  have hjhi : j ≤ 1276847290 := by dsimp [j]; push_cast; nlinarith
  have hlogj : Real.log j < 21 := by
    have h1 := Real.log_le_log hjpos hjhi
    have h2 := log_lt_of_pow_lt_exp 1276847290 21 1 (by norm_num) (by decide) (by norm_num)
    norm_num at h2
    linarith
  have hlog21 : Real.log (21 : ℝ) < 31 / 10 :=
    log_lt_of_pow_lt_exp 21 31 10 (by norm_num) (by decide) (by norm_num)
  have hloglogj : Real.log (Real.log j) < 31 / 10 :=
    lt_of_le_of_lt (Real.log_le_log (Real.log_pos hjone) hlogj.le) hlog21
  have hfactor : Real.log j + Real.log (Real.log j) - 1 / 2 < 118 / 5 := by linarith
  have hu := poolMaximum_upper_sharp upperSharp n (by nlinarith)
  change (poolMaximum n : ℝ) < j * (Real.log j + Real.log (Real.log j) - 1 / 2) at hu
  have hprod := mul_lt_mul_of_pos_left hfactor hjpos
  dsimp [j] at hu hprod
  push_cast at hu hprod
  nlinarith

/-- Reachable diagonal odd-prime supply on `(b, c]` across `19485 ≤ n ≤ 35733`. -/
theorem fw_first_band_diag_prime_supply
    (imp : BMORExplicitFormulaImports)
    (lower : RSIndexLower) (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (b c : ℝ)
    (hb_lo : (4 * 10 ^ 13 : ℝ) < b)
    (hb_X : (5560 : ℝ) * (poolMaximum n : ℝ) ≤ b)
    (hc_hi : c ≤ ((n + 53 : ℕ) : ℝ) * (poolMaximum n : ℝ))
    (hcb : c - b = 52 * (poolMaximum n : ℝ)) :
    (apInterval b c 2 1).Nonempty := by
  have hX_lo : (7365505384 : ℝ) < (poolMaximum n : ℝ) := by
    exact_mod_cast fw_poolMaximum_gt_seven_billion lower hnlo
  have hX_hi : (poolMaximum n : ℝ) ≤ (23601 / 1000 : ℝ) * (n : ℝ) ^ 2 :=
    fw_all_bands_upper_index_ratio upperSharp hnlo hnhi
  have hn_hi : (n : ℝ) ≤ 35733 := by exact_mod_cast hnhi
  have hc_35786 : c ≤ 35786 * (poolMaximum n : ℝ) := by
    have h1 : ((n + 53 : ℕ) : ℝ) ≤ 35786 := by push_cast; linarith
    exact hc_hi.trans (mul_le_mul_of_nonneg_right h1 (by linarith))
  have hc_pow : c ≤ (2 : ℝ) ^ 50 := by
    have hX_val : (poolMaximum n : ℝ) ≤ (23601 / 1000 : ℝ) * 35733 ^ 2 := by
      have hsq : (n : ℝ) ^ 2 ≤ 35733 ^ 2 := pow_le_pow_left₀ (by positivity) hn_hi 2
      linarith
    linarith [show 35786 * ((23601 / 1000 : ℝ) * 35733 ^ 2) ≤ (2 : ℝ) ^ 50 by norm_num]
  have hbc : b ≤ c := by linarith
  have hlog_c : Real.log c ≤ 36 := by
    have h := Real.log_le_log (by linarith) hc_pow
    rw [Real.log_pow] at h
    push_cast at h
    linarith [log_two_lt_frac]
  have hlog_b : Real.log b ≤ 36 :=
    (Real.log_le_log (by linarith) hbc).trans hlog_c
  have htb := abs_le.mp (bmor_theta_mod_two_uniform imp (le_of_lt hb_lo) hlog_b)
  have htc := abs_le.mp (bmor_theta_mod_two_uniform imp (by linarith) hlog_c)
  have hpos : 0 < thetaAP c 2 1 - thetaAP b 2 1 := by
    linarith
  by_contra hempty
  have h0 : apInterval b c 2 1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  rw [thetaAP_sub_eq_interval_sum b c 2 1 hbc, h0] at hpos
  simp at hpos

/-- Window and logarithm bounds for the T75 nominal target interval `[y - D, y + D]`
across `19485 ≤ n ≤ 35733`. -/
theorem fw_t75_nominal_window_bounds
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (y D : ℝ)
    (hy : y = (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue)
    (hD : D = y / 1240) :
    (4 * 10 ^ 13 : ℝ) < y - D ∧
    (32 * 10 ^ 9 : ℝ) < D ∧
    D < ((72 * 2 * 2 ^ 32 : ℕ) : ℝ) ∧
    y + D ≤ (2 : ℝ) ^ 49 ∧
    Real.log (y + D) ≤ 34 := by
  have hy_lo : (4 * 10 ^ 13 : ℝ) < y - D := by
    rw [hy, hD, hy]
    exact fw_t75_nominal_lower_above_finite_bmor bmor lower upper hnlo hnhi
  have hD_lo : (32 * 10 ^ 9 : ℝ) < D := by
    have h : y - D = 1239 * D := by rw [hD]; ring
    linarith
  have hm_hi : centralEntriesMean (prescribedPoolValues n) centralPoolValue ≤
      (123 / 250 : ℝ) * (poolMaximum n : ℝ) := by
    rw [prescribedPoolValues_mean]
    exact (fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo hnhi).2
  have hX_hi : (poolMaximum n : ℝ) ≤ (23601 / 1000 : ℝ) * (n : ℝ) ^ 2 :=
    fw_all_bands_upper_index_ratio upperSharp hnlo hnhi
  have hn_hi : (n : ℝ) ≤ 35733 := by exact_mod_cast hnhi
  have hn_pos : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hy_hi : y ≤ 35733 * ((123 / 250 : ℝ) * ((23601 / 1000 : ℝ) * 35733 ^ 2)) := by
    have hsq : (n : ℝ) ^ 2 ≤ 35733 ^ 2 := pow_le_pow_left₀ hn_pos hn_hi 2
    have hX_val : (poolMaximum n : ℝ) ≤ (23601 / 1000 : ℝ) * 35733 ^ 2 := by linarith
    have hm_val : centralEntriesMean (prescribedPoolValues n) centralPoolValue ≤
        (123 / 250 : ℝ) * ((23601 / 1000 : ℝ) * 35733 ^ 2) := by linarith
    have hy1 : y ≤ (n : ℝ) * ((123 / 250 : ℝ) * ((23601 / 1000 : ℝ) * 35733 ^ 2)) := by
      rw [hy]
      exact mul_le_mul_of_nonneg_left hm_val hn_pos
    linarith
  have hyD_pow : y + D ≤ (2 : ℝ) ^ 49 := by
    rw [hD]
    linarith [show 35733 * ((123 / 250 : ℝ) * ((23601 / 1000 : ℝ) * 35733 ^ 2)) * (1241 / 1240 : ℝ) ≤ (2 : ℝ) ^ 49 by norm_num]
  have hD_hi : D < ((72 * 2 * 2 ^ 32 : ℕ) : ℝ) := by
    rw [hD]
    linarith [show 35733 * ((123 / 250 : ℝ) * ((23601 / 1000 : ℝ) * 35733 ^ 2)) / 1240 < ((72 * 2 * 2 ^ 32 : ℕ) : ℝ) by norm_num]
  have hlog_hi : Real.log (y + D) ≤ 34 := by
    have h := Real.log_le_log (by linarith) hyD_pow
    rw [Real.log_pow] at h
    push_cast at h
    linarith [log_two_lt_frac]
  exact ⟨hy_lo, hD_lo, hD_hi, hyD_pow, hlog_hi⟩

/-- Every interval `(a, b]` with `1 ≤ a ≤ b` has `thetaAP b q r - thetaAP a q r ≤ card * log b`. -/
theorem thetaAP_sub_le_card_mul_log (a b : ℝ) (q : ℕ) (r : ℤ)
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

/-- Favorable-gap seed pair `(r0, r0 + h)` in `[y - D/2, y + D/2]` across `19485 ≤ n ≤ 35733`. -/
theorem fw_t75_seed_pair_supply
    (imp : BMORExplicitFormulaImports)
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (y D : ℝ)
    (hy : y = (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue)
    (hD : D = y / 1240) :
    ∃ h ∈ t75FavorableGaps, ∃ r0 : ℕ,
      Nat.Prime r0 ∧ Nat.Prime (r0 + h) ∧
      y - D / 2 ≤ (r0 : ℝ) ∧ ((r0 + h : ℕ) : ℝ) ≤ y + D / 2 := by
  obtain ⟨hy_lo, hD_lo, _, hyD_pow, hlog_yD⟩ :=
    fw_t75_nominal_window_bounds bmor lower upper upperSharp hnlo hnhi y D hy hD
  let a_s : ℝ := y - (49 / 100 : ℝ) * D
  let b_s : ℝ := y + (49 / 100 : ℝ) * D
  have ha_lo : (4 * 10 ^ 13 : ℝ) ≤ a_s := by dsimp [a_s]; linarith
  have hab : a_s ≤ b_s := by dsimp [a_s, b_s]; linarith
  have hb_le_yD : b_s ≤ y + D := by dsimp [b_s]; linarith
  have hy_eq : y = 1240 * D := by rw [hD]; ring
  have hba_eq : b_s - a_s = (98 / 100 : ℝ) * D := by dsimp [a_s, b_s]; ring
  have hm_bounds := fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo hnhi
  have hm_lo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤
      centralEntriesMean (prescribedPoolValues n) centralPoolValue := by
    rw [prescribedPoolValues_mean]
    exact hm_bounds.1
  have hm_hi : centralEntriesMean (prescribedPoolValues n) centralPoolValue ≤
      (123 / 250 : ℝ) * (poolMaximum n : ℝ) := by
    rw [prescribedPoolValues_mean]
    exact hm_bounds.2
  have hn_pos : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  let S := apInterval a_s b_s 2 1
  have hdense : b_s - a_s + 44 < 35 * (S.card : ℝ) := by
    by_cases h21 : n ≤ 21248
    · have hX_hi : (poolMaximum n : ℝ) ≤ (22501 / 1000 : ℝ) * (n : ℝ) ^ 2 :=
        fw_first_band_upper_index_ratio upperSharp hnlo h21
      have hn_hi : (n : ℝ) ≤ 21248 := by exact_mod_cast h21
      have hsq : (n : ℝ) ^ 2 ≤ 21248 ^ 2 := pow_le_pow_left₀ hn_pos hn_hi 2
      have hy_hi : y ≤ 21248 * ((123 / 250 : ℝ) * ((22501 / 1000 : ℝ) * 21248 ^ 2)) := by
        have hm_val : centralEntriesMean (prescribedPoolValues n) centralPoolValue ≤
            (123 / 250 : ℝ) * ((22501 / 1000 : ℝ) * 21248 ^ 2) := by linarith
        have hy1 : y ≤ (n : ℝ) * ((123 / 250 : ℝ) * ((22501 / 1000 : ℝ) * 21248 ^ 2)) := by
          rw [hy]; exact mul_le_mul_of_nonneg_left hm_val hn_pos
        linarith
      have hb_pow : b_s ≤ (2 : ℝ) ^ 47 := by
        dsimp [b_s]; rw [hD]
        linarith [show 21248 * ((123 / 250 : ℝ) * ((22501 / 1000 : ℝ) * 21248 ^ 2)) * (1241 / 1240 : ℝ) ≤ (2 : ℝ) ^ 47 by norm_num]
      have hlog_b : Real.log b_s ≤ 1629 / 50 := by
        have h := Real.log_le_log (by linarith) hb_pow
        rw [Real.log_pow] at h; push_cast at h; linarith [log_two_lt_frac]
      have hlog_a : Real.log a_s ≤ 36 := (Real.log_le_log (by linarith) hab).trans (by linarith)
      have hta := abs_le.mp (bmor_theta_mod_two_uniform imp ha_lo hlog_a)
      have htb := abs_le.mp (bmor_theta_mod_two_uniform imp (ha_lo.trans hab) (by linarith))
      have hinc_lo : (1163 / 1250 : ℝ) * D ≤ thetaAP b_s 2 1 - thetaAP a_s 2 1 := by
        have hba : b_s - a_s - (a_s + b_s) / 50000 = (1163 / 1250 : ℝ) * D := by
          dsimp [a_s, b_s]; rw [hy_eq]; ring
        linarith [hta.2, htb.1]
      have hinc_hi : thetaAP b_s 2 1 - thetaAP a_s 2 1 ≤ (S.card : ℝ) * (1629 / 50 : ℝ) :=
        (thetaAP_sub_le_card_mul_log a_s b_s 2 1 (by linarith) hab).trans
          (mul_le_mul_of_nonneg_left hlog_b (Nat.cast_nonneg _))
      linarith
    · by_cases hA : n ≤ 27554
      · have hnAlo : 21249 ≤ n := by omega
        have hnAloR : (21249 : ℝ) ≤ n := by exact_mod_cast hnAlo
        have hX_hi : (poolMaximum n : ℝ) ≤ (22974 / 1000 : ℝ) * (n : ℝ) ^ 2 :=
          (fwBandA_envelopes bmor lower upper upperSharp hnAlo hA).1
        let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
        have hjlo : (451520002 : ℝ) ≤ j := by dsimp [j]; push_cast; nlinarith
        have hlogj_lo : (19 : ℝ) < Real.log j := by
          have h1 := lt_log_of_exp_lt_pow 451520002 19 1 (by norm_num) (by decide) (by norm_num)
          norm_num at h1
          exact lt_of_lt_of_le h1 (Real.log_le_log (by norm_num) hjlo)
        have hXlo_raw := poolMaximum_lower lower n
        change j * Real.log j < (poolMaximum n : ℝ) at hXlo_raw
        have hXlo : (8578880038 : ℝ) < poolMaximum n := by nlinarith
        have hy_loA : 21249 * ((243 / 500 : ℝ) * 8578880038) ≤ y := by
          have hm_val : (243 / 500 : ℝ) * 8578880038 ≤ centralEntriesMean (prescribedPoolValues n) centralPoolValue := by linarith
          have hy1 : (21249 : ℝ) * ((243 / 500 : ℝ) * 8578880038) ≤ (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue :=
            mul_le_mul hnAloR hm_val (by positivity) hn_pos
          rwa [← hy] at hy1
        have ha_loA : (88 * 10 ^ 12 : ℝ) ≤ a_s := by
          dsimp [a_s]; rw [hD]; linarith
        have hn_hi : (n : ℝ) ≤ 27554 := by exact_mod_cast hA
        have hsq : (n : ℝ) ^ 2 ≤ 27554 ^ 2 := pow_le_pow_left₀ hn_pos hn_hi 2
        have hy_hi : y ≤ 27554 * ((123 / 250 : ℝ) * ((22974 / 1000 : ℝ) * 27554 ^ 2)) := by
          have hm_val : centralEntriesMean (prescribedPoolValues n) centralPoolValue ≤
              (123 / 250 : ℝ) * ((22974 / 1000 : ℝ) * 27554 ^ 2) := by linarith
          have hy1 : y ≤ (n : ℝ) * ((123 / 250 : ℝ) * ((22974 / 1000 : ℝ) * 27554 ^ 2)) := by
            rw [hy]; exact mul_le_mul_of_nonneg_left hm_val hn_pos
          linarith
        have hb_pow : b_s ≤ (2 : ℝ) ^ 48 := by
          dsimp [b_s]; rw [hD]
          linarith [show 27554 * ((123 / 250 : ℝ) * ((22974 / 1000 : ℝ) * 27554 ^ 2)) * (1241 / 1240 : ℝ) ≤ (2 : ℝ) ^ 48 by norm_num]
        have hlog_b : Real.log b_s ≤ 832 / 25 := by
          have h := Real.log_le_log (by linarith) hb_pow
          rw [Real.log_pow] at h; push_cast at h; linarith [log_two_lt_frac]
        have hlog_a : Real.log a_s ≤ 36 := (Real.log_le_log (by linarith) hab).trans (by linarith)
        have hta := abs_le.mp (bmor_theta_mod_two_bandA imp ha_loA hlog_a)
        have htb := abs_le.mp (bmor_theta_mod_two_bandA imp (ha_loA.trans hab) (by linarith))
        have hinc_lo : (949 / 1000 : ℝ) * D ≤ thetaAP b_s 2 1 - thetaAP a_s 2 1 := by
          have hba : b_s - a_s - (a_s + b_s) / 80000 = (949 / 1000 : ℝ) * D := by
            dsimp [a_s, b_s]; rw [hy_eq]; ring
          linarith [hta.2, htb.1]
        have hinc_hi : thetaAP b_s 2 1 - thetaAP a_s 2 1 ≤ (S.card : ℝ) * (832 / 25 : ℝ) :=
          (thetaAP_sub_le_card_mul_log a_s b_s 2 1 (by linarith) hab).trans
            (mul_le_mul_of_nonneg_left hlog_b (Nat.cast_nonneg _))
        linarith
      · have hnBlo : 27555 ≤ n := by omega
        have hnBloR : (27555 : ℝ) ≤ n := by exact_mod_cast hnBlo
        let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
        have hjlo : (759278026 : ℝ) ≤ j := by dsimp [j]; push_cast; nlinarith
        have hlogj_lo : (20 : ℝ) < Real.log j := by
          have h1 := lt_log_of_exp_lt_pow 759278026 20 1 (by norm_num) (by decide) (by norm_num)
          norm_num at h1
          exact lt_of_lt_of_le h1 (Real.log_le_log (by norm_num) hjlo)
        have hXlo_raw := poolMaximum_lower lower n
        change j * Real.log j < (poolMaximum n : ℝ) at hXlo_raw
        have hXlo : (15185560520 : ℝ) < poolMaximum n := by nlinarith
        have hy_loB : 27555 * ((243 / 500 : ℝ) * 15185560520) ≤ y := by
          have hm_val : (243 / 500 : ℝ) * 15185560520 ≤ centralEntriesMean (prescribedPoolValues n) centralPoolValue := by linarith
          have hy1 : (27555 : ℝ) * ((243 / 500 : ℝ) * 15185560520) ≤ (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue :=
            mul_le_mul hnBloR hm_val (by positivity) hn_pos
          rwa [← hy] at hy1
        have ha_loB : (200 * 10 ^ 12 : ℝ) ≤ a_s := by
          dsimp [a_s]; rw [hD]; linarith
        have hb_pow : b_s ≤ (2 : ℝ) ^ 49 := hb_le_yD.trans hyD_pow
        have hlog_b : Real.log b_s ≤ 3397 / 100 := by
          have h := Real.log_le_log (by linarith) hb_pow
          rw [Real.log_pow] at h; push_cast at h; linarith [log_two_lt_frac]
        have hlog_a : Real.log a_s ≤ 36 := (Real.log_le_log (by linarith) hab).trans (by linarith)
        have hta := abs_le.mp (bmor_theta_mod_two_bandB imp ha_loB hlog_a)
        have htb := abs_le.mp (bmor_theta_mod_two_bandB imp (ha_loB.trans hab) (by linarith))
        have hinc_lo : (11022 / 11500 : ℝ) * D ≤ thetaAP b_s 2 1 - thetaAP a_s 2 1 := by
          have hba : b_s - a_s - (a_s + b_s) / 115000 = (11022 / 11500 : ℝ) * D := by
            dsimp [a_s, b_s]; rw [hy_eq]; ring
          linarith [hta.2, htb.1]
        have hinc_hi : thetaAP b_s 2 1 - thetaAP a_s 2 1 ≤ (S.card : ℝ) * (3397 / 100 : ℝ) :=
          (thetaAP_sub_le_card_mul_log a_s b_s 2 1 (by linarith) hab).trans
            (mul_le_mul_of_nonneg_left hlog_b (Nat.cast_nonneg _))
        linarith
  have hS_prime : ∀ p ∈ S, 5 < p ∧ Nat.Prime p := by
    intro p hp
    have ⟨hp_prime, ha_lt, _, _⟩ := (mem_apInterval_iff a_s b_s 2 1 (by linarith) (by linarith) p).mp hp
    have hp5 : (5 : ℝ) < (p : ℝ) := by linarith
    exact ⟨by exact_mod_cast hp5, hp_prime⟩
  have hS_int : ∀ p ∈ S, a_s ≤ (p : ℝ) ∧ (p : ℝ) ≤ b_s := by
    intro p hp
    have ⟨_, ha_lt, hb_le, _⟩ := (mem_apInterval_iff a_s b_s 2 1 (by linarith) (by linarith) p).mp hp
    exact ⟨le_of_lt ha_lt, hb_le⟩
  obtain ⟨r0, hr0_mem, h, hh_mem, hr0h_mem⟩ :=
    exists_favorable_gap_pair_in_finset S a_s b_s hS_prime hS_int hab hdense
  refine ⟨h, hh_mem, r0, (hS_prime r0 hr0_mem).2, (hS_prime (r0 + h) hr0h_mem).2, ?_, ?_⟩
  · have := (hS_int r0 hr0_mem).1
    dsimp [a_s] at this
    linarith
  · have := (hS_int (r0 + h) hr0h_mem).2
    dsimp [b_s] at this
    linarith

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

/-- Unified lower bound on `φ(h) * (thetaAP v h r - thetaAP u h r)` across all `h ∈ t75FavorableGaps`
    (including `h = 2` via `bmor_theta_mod_two_uniform` and `h = 42` via modulus `21`) on any
    subinterval `[u, v] ⊆ [y - D, y + D]`. -/
theorem fw_t75_theta_increment_lower
    (imp : BMORExplicitFormulaImports)
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp)
    {n h r : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hh : h ∈ t75FavorableGaps) (hr : r < h) (hcop : Nat.Coprime r h)
    (y D : ℝ)
    (hy : y = (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue)
    (hD : D = y / 1240)
    {u v : ℝ}
    (hu : y - D ≤ u) (huv : u ≤ v) (hv : v ≤ y + D) :
    (Nat.totient h : ℝ) * (thetaAP v h (r : ℤ) - thetaAP u h (r : ℤ)) ≥
      (v - u) - (u + v) / 5000 := by
  obtain ⟨hy_lo, _, _, _, hlog_yD⟩ :=
    fw_t75_nominal_window_bounds bmor lower upper upperSharp hnlo hnhi y D hy hD
  have hu_lo : (4 * 10 ^ 13 : ℝ) ≤ u := (le_of_lt hy_lo).trans hu
  have hv_lo : (4 * 10 ^ 13 : ℝ) ≤ v := hu_lo.trans huv
  have hlog_v : Real.log v ≤ 36 :=
    (Real.log_le_log (by linarith) hv).trans (by linarith)
  have hlog_u : Real.log u ≤ 36 :=
    (Real.log_le_log (by linarith) huv).trans hlog_v
  by_cases h2 : h = 2
  · subst h
    have hr1 : r = 1 := by
      rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
      · exfalso
        exact absurd hcop (by decide)
      · rfl
    subst r
    have htu := abs_le.mp (bmor_theta_mod_two_uniform imp hu_lo hlog_u)
    have htv := abs_le.mp (bmor_theta_mod_two_uniform imp hv_lo hlog_v)
    have htot2 : (Nat.totient 2 : ℝ) = 1 := by norm_num
    rw [htot2]
    push_cast
    linarith
  · obtain ⟨q, hq_def, hq3, hq36, hphi12, hphi_eq, hcop_q⟩ :=
      favorable_gap_reduced_modulus hh h2 hr hcop
    have htu := abs_le.mp (bmor_theta_small_moduli_signed imp hq3 hq36 hphi12 hcop_q hu_lo hlog_u)
    have htv := abs_le.mp (bmor_theta_small_moduli_signed imp hq3 hq36 hphi12 hcop_q hv_lo hlog_v)
    have hinc_eq : thetaAP v h (r : ℤ) - thetaAP u h (r : ℤ) =
        thetaAP v q ((r % q : ℕ) : ℤ) - thetaAP u q ((r % q : ℕ) : ℤ) := by
      by_cases h42 : h = 42
      · subst h
        rw [hq_def, if_pos rfl]
        exact thetaAP_forty_two_increment_eq_twenty_one (by linarith) huv hr hcop
      · rw [hq_def, if_neg h42, Nat.mod_eq_of_lt hr]
    rw [hinc_eq, hphi_eq]
    linarith

/-- Construct the first-band T75 prime target vector `f : Fin n → ℕ` from
    `BMORExplicitFormulaImports`, `BMORFiniteTheta`, and `RSIndexImports`. -/
theorem fw_t75_nominal_targets_of_explicit_formula
    (imp : BMORExplicitFormulaImports)
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hn : Odd n) :
    let y : ℝ := (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let D : ℝ := y / 1240
    ∃ f : Fin n → ℕ,
      (∑ i, f i) = Lucas.poolTotal n ∧
      (∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ) - y| ≤ D) := by
  dsimp only
  let y : ℝ := (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue
  let D : ℝ := y / 1240
  obtain ⟨hy_lo, hD_lo, hD_2, hyD_pow, hlog_yD⟩ :=
    fw_t75_nominal_window_bounds bmor lower upper upperSharp hnlo hnhi y D rfl rfl
  obtain ⟨h, hh, r0, hr0_prime, hr0h_prime, hr0_lo, hr0_hi⟩ :=
    fw_t75_seed_pair_supply imp bmor lower upper upperSharp hnlo hnhi y D rfl rfl
  have hh_basic := favorable_gap_basic_props h hh
  have hh_2 : 2 ≤ h := hh_basic.1
  have hh_42 : h ≤ 42 := hh_basic.2.1
  have hD_upper : D < ((72 * h * 2 ^ 32 : ℕ) : ℝ) := by
    have hle : 72 * 2 * 2 ^ 32 ≤ 72 * h * 2 ^ 32 := by omega
    exact lt_of_lt_of_le hD_2 (by exact_mod_cast hle)
  have hy_eq : y = 1240 * D := by dsimp [D]; ring
  have hpos_half : ∀ r : ℕ, r < h → Nat.Coprime r h →
      ∀ u v : ℝ, y - D ≤ u → v ≤ y + D → D / 2 ≤ v - u →
      0 < thetaAP v h (r : ℤ) - thetaAP u h (r : ℤ) := by
    intro r hr hcop u v hu hv hw
    have hinc := fw_t75_theta_increment_lower imp bmor lower upper upperSharp hnlo hnhi hh hr hcop
      y D rfl rfl hu (by linarith) hv
    have hpos_mul : 0 < (Nat.totient h : ℝ) * (thetaAP v h (r : ℤ) - thetaAP u h (r : ℤ)) := by
      linarith
    have hphi_pos : (0 : ℝ) < (Nat.totient h : ℝ) :=
      Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
    exact pos_of_mul_pos_right hpos_mul (le_of_lt hphi_pos)
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
  have hA_inc_lo := fw_t75_theta_increment_lower imp bmor lower upper upperSharp hnlo hnhi hh h1_lt h1_cop
    y D rfl rfl (u := y - D / 2) (v := y + D / 2) (by linarith) (by linarith) (by linarith)
  have hlog_mid : Real.log (y + D / 2) ≤ 34 :=
    (Real.log_le_log (by linarith) (by linarith : y + D / 2 ≤ y + D)).trans (by linarith)
  have hA_inc_hi : thetaAP (y + D / 2) h 1 - thetaAP (y - D / 2) h 1 ≤ (A.card : ℝ) * 34 := by
    have h1 := thetaAP_sub_le_card_mul_log (y - D / 2) (y + D / 2) h 1 (by linarith) (by linarith)
    have h2 : (A.card : ℝ) * Real.log (y + D / 2) ≤ (A.card : ℝ) * 34 :=
      mul_le_mul_of_nonneg_left hlog_mid (Nat.cast_nonneg _)
    exact h1.trans h2
  have hphi_2 : 2 * (Nat.totient h : ℝ) ≤ (h : ℝ) := by
    exact_mod_cast hh_basic.2.2
  have hphi_pos : (0 : ℝ) ≤ (Nat.totient h : ℝ) := Nat.cast_nonneg _
  have hphi_card : (Nat.totient h : ℝ) * (thetaAP (y + D / 2) h 1 - thetaAP (y - D / 2) h 1) ≤
      17 * (h : ℝ) * (A.card : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hA_inc_hi hphi_pos,
               mul_le_mul_of_nonneg_right hphi_2 (Nat.cast_nonneg A.card)]
  have hA_card : D < 36 * (h : ℝ) * (A.card : ℝ) := by
    linarith
  have hA_card_ge : 2 ≤ A.card := by
    have hh_hi : (h : ℝ) ≤ 42 := by exact_mod_cast hh_42
    have hcard_real : (2 : ℝ) ≤ (A.card : ℝ) := by nlinarith
    exact_mod_cast hcard_real
  exact fw_t75_nominal_targets_from_supplies bmor lower upper hnlo hnhi hn hh y D rfl rfl hD_upper
    hsupply r0 hr0_prime hr0h_prime hr0_lo hr0_hi A hA_prime hA_int hA_mod hA_card_ge hA_card
    uw vw huw_prime hvw_prime huw_mod' hvw_mod' ⟨le_of_lt huw_lo, huw_hi⟩ ⟨le_of_lt hvw_lo, hvw_hi⟩

/-- Complete `HasSquare n` theorem across `19485 ≤ n ≤ 35733, Odd n` from
    published analytic hypotheses and a twin-prime seed Finset `seeds`. -/
theorem fw_first_band_hasSquare_of_seeds
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta)
    (imp : BMORExplicitFormulaImports)
    (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hodd : Odd n)
    (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hseedPrime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hseedCount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    HasSquare n := by
  obtain ⟨target, htotal, hvalid⟩ :=
    fw_t75_nominal_targets_of_explicit_formula imp bmor lower upper upperSharp hnlo hnhi hodd
  exact fw_theta_fresh_first_band_hasSquare_of_targets_and_diag_prime
    mv bmor upper lower sharp upperSharp hnlo hnhi hodd
    seeds hseed hseedPrime hseedCount
    target (fun i => (hvalid i).1) (fun i => (hvalid i).2.1) htotal (fun i => (hvalid i).2.2)
    (fun b c hb_lo hb_X hc_hi hcb =>
      fw_first_band_diag_prime_supply imp lower upperSharp hnlo hnhi b c hb_lo hb_X hc_hi hcb)

end

end Sude
