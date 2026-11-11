import Sude.FC2KT75AnalyticSupply
import Sude.FC2KBridgeAndDiagonalHelpers
import Sude.GlobalPoolMeanBounds
import Sude.MontgomeryVaughan

/-!
# Unified All-Scale Analytic Supply for the Open Upper Tail (`n ≥ 35,735`)

This module combines:
1. `BMORFiniteTheta` (for scales `x ≤ 10 ^ 13` / `4 * 10 ^ 13`),
2. `BMORExplicitFormulaImports` via `bmor_theta_mod_two_all_ge_7e12` and
   `bmor_theta_small_moduli_all_ge_7e12` (for all scales `x ≥ 7 * 10 ^ 12`, unbounded above),
3. `MVBrunTitchmarsh` (for progressions modulo `2 * p` with prime `p ≥ 5`),

to provide scale-free interval prime counts and single-class modulo-`2p` upper bounds
for all `x ≥ 2.5 * 10 ^ 7`.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false

/-! ## Interval Count Upper Bound from `thetaAP` -/

/-- Every prime `p ∈ apInterval b c q a` satisfies `b < p`, so `Real.log b ≤ Real.log p`
when `1 ≤ b`. -/
theorem ut_count_log_le_thetaAP_interval (b c : ℝ) (q : ℕ) (a : ℤ)
    (hb : 1 ≤ b) (hbc : b ≤ c) :
    ((apInterval b c q a).card : ℝ) * Real.log b ≤
      thetaAP c q a - thetaAP b q a := by
  have hb0 : 0 ≤ b := by linarith
  rw [thetaAP_sub_eq_interval_sum b c q a hbc]
  calc
    ((apInterval b c q a).card : ℝ) * Real.log b =
        ∑ _p ∈ apInterval b c q a, Real.log b := by simp
    _ ≤ ∑ p ∈ apInterval b c q a, Real.log p := by
      apply Finset.sum_le_sum
      intro p hp
      have hm := (mem_apInterval_iff b c q a hb0 (hb0.trans hbc) p).mp hp
      exact Real.log_le_log (by linarith) (le_of_lt hm.2.1)

/-! ## Unified All-Scale `thetaAP` Bounds -/

/-- Across all scales `x ≥ 2.5 * 10 ^ 7`, `|thetaAP x 2 1 - x| ≤ x / 1000`. -/
theorem thetaAP_mod_two_all_scales
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    {x : ℝ} (hx : (25 * 10 ^ 6 : ℝ) ≤ x) :
    |thetaAP x 2 1 - x| ≤ x / 1000 := by
  by_cases hcap : x ≤ (4 * 10 ^ 13 : ℝ)
  · have hx1 : (1 : ℝ) ≤ x := by linarith
    have hbmor := bmor_theta_two_via_four bmor x hx1 hcap
    have hs_ge : (5000 : ℝ) ≤ Real.sqrt x := by
      have hsq : (5000 : ℝ) ^ 2 ≤ x := by
        linarith [show (5000 : ℝ) ^ 2 = 25 * 10 ^ 6 by norm_num]
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5000)]
      exact Real.sqrt_le_sqrt hsq
    have hsqrt_le : Real.sqrt x ≤ x / 5000 := by
      have hmul : (5000 : ℝ) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hs_ge (Real.sqrt_nonneg x)
      rw [Real.mul_self_sqrt (by linarith)] at hmul
      linarith
    linarith
  · have h7e12 : (7 * 10 ^ 12 : ℝ) ≤ x := by linarith
    have himp := bmor_theta_mod_two_all_ge_7e12 imp h7e12
    linarith

/-- Across all scales `x ≥ 5 * 10 ^ 9`, `|thetaAP x 2 1 - x| ≤ x / 12000`. -/
theorem thetaAP_mod_two_all_ge_5e9
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    {x : ℝ} (hx : (5 * 10 ^ 9 : ℝ) ≤ x) :
    |thetaAP x 2 1 - x| ≤ x / 12000 := by
  by_cases hcap : x ≤ (4 * 10 ^ 13 : ℝ)
  · have hx1 : (1 : ℝ) ≤ x := by linarith
    have hbmor := bmor_theta_two_via_four bmor x hx1 hcap
    have hs_ge : (70710 : ℝ) ≤ Real.sqrt x := by
      have hsq : (70710 : ℝ) ^ 2 ≤ x := by
        linarith [show (70710 : ℝ) ^ 2 ≤ 5 * 10 ^ 9 by norm_num]
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 70710)]
      exact Real.sqrt_le_sqrt hsq
    have hsqrt_le : Real.sqrt x ≤ x / 70710 := by
      have hmul : (70710 : ℝ) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hs_ge (Real.sqrt_nonneg x)
      rw [Real.mul_self_sqrt (by linarith)] at hmul
      linarith
    linarith
  · have h7e12 : (7 * 10 ^ 12 : ℝ) ≤ x := by linarith
    have himp := bmor_theta_mod_two_all_ge_7e12 imp h7e12
    linarith

/-- Across all scales `x ≥ 5 * 10 ^ 9`, for `q ∈ [3, 36]` with `φ(q) = 2` and `gcd(q, a) = 1`,
`|thetaAP x q a - x / 2| ≤ x / 25000`. -/
theorem thetaAP_totient_two_all_scales
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    {q : ℕ} {a : ℤ} {x : ℝ}
    (hq_min : 3 ≤ q) (hq_max : q ≤ 36) (hphi : Nat.totient q = 2)
    (hcop : Nat.Coprime q a.natAbs) (hx : (5 * 10 ^ 9 : ℝ) ≤ x) :
    |thetaAP x q a - x / 2| ≤ x / 25000 := by
  have hphiR : (Nat.totient q : ℝ) = 2 := by exact_mod_cast hphi
  by_cases hcap : x ≤ (10 ^ 13 : ℝ)
  · have hx1 : (1 : ℝ) ≤ x := by linarith
    have hbmor := bmor_theta_bounded bmor q a x hq_min (by omega) hcop hx1 hcap
    rw [hphiR] at hbmor
    have hs_ge : (70710 : ℝ) ≤ Real.sqrt x := by
      have hsq : (70710 : ℝ) ^ 2 ≤ x := by
        linarith [show (70710 : ℝ) ^ 2 ≤ 5 * 10 ^ 9 by norm_num]
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 70710)]
      exact Real.sqrt_le_sqrt hsq
    have hsqrt_le : Real.sqrt x ≤ x / 70710 := by
      have hmul : (70710 : ℝ) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hs_ge (Real.sqrt_nonneg x)
      rw [Real.mul_self_sqrt (by linarith)] at hmul
      linarith
    linarith
  · have h7e12 : (7 * 10 ^ 12 : ℝ) ≤ x := by linarith
    have hx_pos : 0 < x := by linarith
    have hpi_lo : (314 / 100 : ℝ) < Real.pi := by
      have h := Real.pi_gt_d2; norm_num at h ⊢; exact h
    have hpi_hi : Real.pi < (315 / 100 : ℝ) := by
      have h := Real.pi_lt_d2; norm_num at h ⊢; exact h
    have hlog2_lo : (6931471803 / 10000000000 : ℝ) < Real.log 2 := by
      have h := Real.log_two_gt_d9; norm_num at h ⊢; exact h
    have hlog2_hi : Real.log 2 < (6931471808 / 10000000000 : ℝ) := by
      have h := Real.log_two_lt_d9; norm_num at h ⊢; exact h
    have hlam_lo : (18 : ℝ) ≤ Real.log (10 ^ 8 : ℝ) := by
      have hle : (2 : ℝ) ^ 26 ≤ 10 ^ 8 := by norm_num
      have h := Real.log_le_log (by positivity) hle
      rw [Real.log_pow] at h; push_cast at h; linarith
    have hlam_hi : Real.log (10 ^ 8 : ℝ) ≤ 19 := by
      have hle : (10 ^ 8 : ℝ) ≤ (2 : ℝ) ^ 27 := by norm_num
      have h := Real.log_le_log (by positivity) hle
      rw [Real.log_pow (2 : ℝ) 27] at h; push_cast at h; linarith
    have hlog_lo : (28 : ℝ) ≤ Real.log x := by
      have h2_42 : (2 : ℝ) ^ 42 ≤ x := by linarith [show (2 : ℝ) ^ 42 ≤ 7 * 10 ^ 12 by norm_num]
      have h := Real.log_le_log (by positivity) h2_42
      rw [Real.log_pow] at h; push_cast at h; linarith
    have hs_ge : (2645751 : ℝ) ≤ Real.sqrt x := by
      have hsq : (2645751 : ℝ) ^ 2 ≤ x := by linarith [show (2645751 : ℝ) ^ 2 ≤ 7 * 10 ^ 12 by norm_num]
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2645751)]
      exact Real.sqrt_le_sqrt hsq
    have hsqrt_le : Real.sqrt x ≤ x / 2645751 := by
      have hmul : (2645751 : ℝ) * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hs_ge (Real.sqrt_nonneg x)
      rw [Real.mul_self_sqrt hx_pos.le] at hmul; linarith
    have hlog_sub : 25 * Real.log x + 62 ≤ (1 / 10 : ℝ) * Real.sqrt x := by
      let s := Real.sqrt x
      have hs_pos : 0 < s := by dsimp [s]; linarith
      let r0 := Real.sqrt s
      have hr0_ge : (1626 : ℝ) ≤ r0 := by
        have hsq : (1626 : ℝ) ^ 2 ≤ s := by
          dsimp [s]; linarith [show (1626 : ℝ) ^ 2 ≤ 2645751 by norm_num]
        dsimp [r0]
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1626)]
        exact Real.sqrt_le_sqrt hsq
      have hr0_pos : 0 < r0 := by linarith
      have hr0_le : r0 ≤ s / 1626 := by
        have hmul : (1626 : ℝ) * r0 ≤ r0 * r0 := mul_le_mul_of_nonneg_right hr0_ge hr0_pos.le
        rw [Real.mul_self_sqrt hs_pos.le] at hmul; linarith
      have hlog_r0 : Real.log r0 ≤ r0 - 1 := Real.log_le_sub_one_of_pos hr0_pos
      have hlog_s : Real.log s = 2 * Real.log r0 := by
        dsimp [r0]; rw [Real.log_sqrt hs_pos.le]; ring
      have hlog_x : Real.log x = 2 * Real.log s := by
        dsimp [s]; rw [Real.log_sqrt hx_pos.le]; ring
      linarith
    have hK0 : bmorLowZeroCap (36 : ℝ) ((10 ^ 8 : ℝ) / 36) ≤ 68 := by
      unfold bmorLowZeroCap bmorC1 bmorC2
      dsimp only
      let ν := Real.log (36 : ℝ)
      let lam := Real.log ((36 : ℝ) * ((10 ^ 8 : ℝ) / 36))
      let c := Real.log (2 * Real.pi) + 1
      have hν_hi : ν ≤ 5 := by
        have hle : (36 : ℝ) ≤ (2 : ℝ) ^ 6 := by norm_num
        have h := Real.log_le_log (by positivity) hle
        rw [Real.log_pow] at h; dsimp [ν]; push_cast at h; linarith
      have hc_lo : (2 : ℝ) ≤ c := by
        have h4 : (2 : ℝ) ^ 2 ≤ 2 * Real.pi := by linarith
        have h := Real.log_le_log (by positivity) h4
        rw [Real.log_pow] at h; dsimp [c]; push_cast at h; linarith
      have hlam_eq : lam = Real.log (10 ^ 8 : ℝ) := by dsimp [lam]; congr 1; norm_num
      have hlam_hi' : lam ≤ 19 := by rw [hlam_eq]; exact hlam_hi
      have hlam_lo' : c ≤ lam := by
        rw [hlam_eq]
        have h2pi : 2 * Real.pi ≤ (2 : ℝ) ^ 3 := by linarith
        have h := Real.log_le_log (by positivity) h2pi
        rw [Real.log_pow] at h; dsimp [c]; push_cast at h; linarith
      have hquad1 : (ν - c) - (ν - c) ^ 2 / 2 ≤ 1 / 2 := by
        have hsq : 0 ≤ ((ν - c) - 1) ^ 2 := sq_nonneg _
        linarith
      have hdiff_hi : lam - c ≤ 17 := by linarith
      have hdiff_lo : 0 ≤ lam - c := by linarith
      have hquad2 : (lam - c) + (lam - c) ^ 2 / 2 ≤ 17 + 17 ^ 2 / 2 := by nlinarith
      have hnum : (ν - c) + (lam - c) + ((lam - c) ^ 2 - (ν - c) ^ 2) / 2 ≤ 162 := by linarith
      have hdiv : ((ν - c) + (lam - c) + ((lam - c) ^ 2 - (ν - c) ^ 2) / 2) / Real.pi ≤
          162 / (314 / 100 : ℝ) := by
        have h1 : ((ν - c) + (lam - c) + ((lam - c) ^ 2 - (ν - c) ^ 2) / 2) / Real.pi ≤
            162 / Real.pi := div_le_div_of_nonneg_right hnum (by positivity)
        have h2 : (162 : ℝ) / Real.pi ≤ 162 / (314 / 100 : ℝ) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi_lo.le
        exact h1.trans h2
      change ((ν - c) + (lam - c) + ((lam - c) ^ 2 - (ν - c) ^ 2) / 2) / Real.pi +
        2 * (399 / 1000) * ν + 399 / 1000 + 2 * (5338 / 1000) - (399 / 1000) / ((10 ^ 8 : ℝ) / 36) ≤ 68
      linarith
    have har_lo : (9 : ℝ) ≤ (10 : ℝ) - 28 / (bmorZeroFreeR * (Real.log (10 ^ 8 : ℝ)) ^ 2) := by
      unfold bmorZeroFreeR
      have hsq : (18 : ℝ) ^ 2 ≤ (Real.log (10 ^ 8 : ℝ)) ^ 2 := pow_le_pow_left₀ (by norm_num) hlam_lo 2
      have hmul_sq : (28 / 5 : ℝ) * 18 ^ 2 ≤ (28 / 5 : ℝ) * (Real.log (10 ^ 8 : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
      have hdiv : 28 / ((28 / 5 : ℝ) * (Real.log (10 ^ 8 : ℝ)) ^ 2) ≤ 28 / ((28 / 5 : ℝ) * 18 ^ 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hmul_sq
      linarith
    have hpt := bmor_theta_small_moduli_pointwise imp
      (q := q) (Q := 36) (a := a) (r := 10) (Φ := 2) (τ := 4 / 10 ^ 6) (z := 28) (K0 := 68) (x := x)
      hq_min hq_max (by decide) hcop (by rw [hphiR]) (by decide) (by norm_num) (by norm_num)
      (by norm_num) (by linarith) hK0 (by norm_num) (by linarith) hlog_lo
    have hsmooth : bmorSmoothFactor 10 (4 / 10 ^ 6 : ℝ) ≤ ((4 / 10 ^ 6 : ℝ) ^ 10)⁻¹ * 2048 := by
      unfold bmorSmoothFactor
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hterm : ∀ j ∈ Finset.range 11,
          (Nat.choose 10 j : ℝ) * (1 + (j : ℝ) * (4 / 10 ^ 6 : ℝ)) ^ 11 ≤ (Nat.choose 10 j : ℝ) * 2 := by
        intro j hj
        have hj_le : (j : ℝ) ≤ 10 := by exact_mod_cast (show j ≤ 10 by have := Finset.mem_range.mp hj; omega)
        have h1 : 1 + (j : ℝ) * (4 / 10 ^ 6 : ℝ) ≤ 1 + 10 * (4 / 10 ^ 6 : ℝ) := by nlinarith
        have hp1 : (1 + (j : ℝ) * (4 / 10 ^ 6 : ℝ)) ^ 11 ≤ (1 + 10 * (4 / 10 ^ 6 : ℝ)) ^ 11 :=
          pow_le_pow_left₀ (by positivity) h1 11
        have hp2 : (1 + 10 * (4 / 10 ^ 6 : ℝ)) ^ 11 ≤ 2 := by norm_num
        exact mul_le_mul_of_nonneg_left (hp1.trans hp2) (Nat.cast_nonneg _)
      have hsum_nat : (∑ j ∈ Finset.range 11, Nat.choose 10 j * 2) = 2048 := by decide
      have hsum_real : (∑ j ∈ Finset.range 11, (Nat.choose 10 j : ℝ) * 2) = 2048 := by exact_mod_cast hsum_nat
      exact (Finset.sum_le_sum hterm).trans (le_of_eq hsum_real)
    have hhigh : bmorHighZeroSum (36 : ℝ) 2 28 10 ≤ (2 / (2 * ((10 ^ 8 : ℝ) / 36) ^ 10)) * 2 := by
      unfold bmorHighZeroSum bmorC1 bmorC2 bmorZeroFreeR
      dsimp only
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      let lam := Real.log (10 ^ 8 : ℝ)
      let ar := (10 : ℝ) - 28 / ((28 / 5 : ℝ) * lam ^ 2)
      have har9 : 9 ≤ ar := har_lo
      have har_sq : 81 ≤ ar ^ 2 := by nlinarith
      have hBr : (lam / ar + 1 / ar ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36) ≤ 1 := by
        have h1 : lam / ar ≤ 19 / 9 :=
          (div_le_div_of_nonneg_right hlam_hi (by linarith)).trans
            (div_le_div_of_nonneg_left (by norm_num) (by norm_num) har9)
        have h2 : 1 / ar ^ 2 ≤ 1 / 81 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) har_sq
        have h3 : (lam / ar + 1 / ar ^ 2) / Real.pi ≤ (19 / 9 + 1 / 81) / (314 / 100 : ℝ) :=
          (div_le_div_of_nonneg_right (by linarith) (by positivity)).trans
            (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi_lo.le)
        linarith
      have hBr0 : (lam / 10 + 1 / (10 : ℝ) ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36) ≤ 1 := by
        have h1 : (lam / 10 + 1 / (10 : ℝ) ^ 2) / Real.pi ≤ (19 / 10 + 1 / 100) / (314 / 100 : ℝ) :=
          (div_le_div_of_nonneg_right (by linarith) (by positivity)).trans
            (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi_lo.le)
        linarith
      have hexp1 : Real.exp (-28 / ((28 / 5 : ℝ) * lam)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith)
      have hexp2 : Real.exp (-28 / 2 : ℝ) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
      have hBr_nn : 0 ≤ (lam / ar + 1 / ar ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36) := by
        have : 0 < ar := by linarith
        positivity
      have hBr0_nn : 0 ≤ (lam / 10 + 1 / (10 : ℝ) ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36) := by
        positivity
      have hp1 := mul_le_mul hexp1 hBr hBr_nn (by norm_num)
      have hp2 := mul_le_mul hexp2 hBr0 hBr0_nn (by norm_num)
      change Real.exp (-28 / ((28 / 5 : ℝ) * lam)) *
          ((lam / ar + 1 / ar ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36)) +
        Real.exp (-28 / 2 : ℝ) *
          ((lam / 10 + 1 / (10 : ℝ) ^ 2) / Real.pi + 2 * (399 / 1000 * lam + 5338 / 1000) / ((10 ^ 8 : ℝ) / 36)) ≤ 2
      linarith
    have hhigh_nn : 0 ≤ bmorHighZeroSum (36 : ℝ) 2 28 10 := by
      unfold bmorHighZeroSum bmorC1 bmorC2 bmorZeroFreeR; dsimp only
      have : 0 < (10 : ℝ) - 28 / ((28 / 5 : ℝ) * (Real.log (10 ^ 8 : ℝ)) ^ 2) := by
        unfold bmorZeroFreeR at har_lo; linarith
      positivity
    have hprod_high : bmorSmoothFactor 10 (4 / 10 ^ 6 : ℝ) * bmorHighZeroSum (36 : ℝ) 2 28 10 ≤ 1 / 10 ^ 6 := by
      have h1 := mul_le_mul hsmooth hhigh hhigh_nn (by positivity)
      have h2 : (((4 / 10 ^ 6 : ℝ) ^ 10)⁻¹ * 2048) * ((2 / (2 * ((10 ^ 8 : ℝ) / 36) ^ 10)) * 2) ≤ 1 / 10 ^ 6 := by
        norm_num
      exact h1.trans h2
    have hmain : ((10 : ℝ) * (4 / 10 ^ 6 : ℝ) / 2 +
        bmorSmoothFactor 10 (4 / 10 ^ 6 : ℝ) * bmorHighZeroSum (36 : ℝ) 2 28 10) * x ≤
        (2 / 10 ^ 5 + 1 / 10 ^ 6) * x := by nlinarith
    rw [hphiR] at hpt
    norm_num at hpt
    linarith

/-! ## Unified Odd-Prime Interval Cardinality Bounds -/

/-- All-scale odd-prime interval lower bound for `2.5 * 10 ^ 7 ≤ b ≤ c ≤ X`. -/
theorem apInterval_mod_two_card_lower_all_scales
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    {b c X : ℝ} (hb : (25 * 10 ^ 6 : ℝ) ≤ b) (hbc : b ≤ c) (hcX : c ≤ X) :
    ((c - b) - (b + c) / 1000) / Real.log X ≤ (apInterval b c 2 1).card := by
  have hX1 : 1 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos hX1
  have hupper := thetaAP_interval_le_count_log b c X 2 1 (by linarith) hbc hcX
  have hB := (abs_le.mp (thetaAP_mod_two_all_scales bmor imp hb)).2
  have hC := (abs_le.mp (thetaAP_mod_two_all_scales bmor imp (hb.trans hbc))).1
  rw [div_le_iff₀ hlog]
  linarith

/-- Sharp all-scale odd-prime interval lower bound for `5 * 10 ^ 9 ≤ b ≤ c ≤ X`. -/
theorem apInterval_mod_two_card_lower_ge_5e9
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    {b c X : ℝ} (hb : (5 * 10 ^ 9 : ℝ) ≤ b) (hbc : b ≤ c) (hcX : c ≤ X) :
    ((c - b) - (b + c) / 12000) / Real.log X ≤ (apInterval b c 2 1).card := by
  have hX1 : 1 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos hX1
  have hupper := thetaAP_interval_le_count_log b c X 2 1 (by linarith) hbc hcX
  have hB := (abs_le.mp (thetaAP_mod_two_all_ge_5e9 bmor imp hb)).2
  have hC := (abs_le.mp (thetaAP_mod_two_all_ge_5e9 bmor imp (hb.trans hbc))).1
  rw [div_le_iff₀ hlog]
  linarith

/-- All-scale odd-prime interval upper bound for `2.5 * 10 ^ 7 ≤ b ≤ c`. -/
theorem apInterval_mod_two_card_upper_all_scales
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    {b c : ℝ} (hb : (25 * 10 ^ 6 : ℝ) ≤ b) (hbc : b ≤ c) :
    ((apInterval b c 2 1).card : ℝ) ≤ ((c - b) + (b + c) / 1000) / Real.log b := by
  have hb1 : 1 < b := by linarith
  have hlog : 0 < Real.log b := Real.log_pos hb1
  have hlower := ut_count_log_le_thetaAP_interval b c 2 1 (by linarith) hbc
  have hB := (abs_le.mp (thetaAP_mod_two_all_scales bmor imp hb)).1
  have hC := (abs_le.mp (thetaAP_mod_two_all_scales bmor imp (hb.trans hbc))).2
  rw [le_div_iff₀ hlog]
  linarith

/-! ## Uniform Modulo-`2p` Single-Class Upper Bound for All Primes `p < b` -/

/-- Any prime `p` is either `2`, `3`, or `≥ 5`. -/
private theorem prime_eq_two_or_three_or_ge_five {p : ℕ} (hp : Nat.Prime p) :
    p = 2 ∨ p = 3 ∨ 5 ≤ p := by
  have h2 : 2 ≤ p := hp.two_le
  by_cases h4 : p = 4
  · subst h4; exact absurd hp (by decide)
  · omega

/-- Uniform single-class upper bound modulo `2 * p` on `apInterval b c 2 1` for every prime `p < b`,
combining BMOR (`p ∈ {2, 3}`, `2 * p ∈ {4, 6}`) and Montgomery–Vaughan (`p ≥ 5`). -/
theorem apInterval_filter_mod_two_prime_le
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports) (mv : MVBrunTitchmarsh)
    {b c : ℝ} {p r : ℕ}
    (hp : Nat.Prime p)
    (hb : (5 * 10 ^ 9 : ℝ) ≤ b)
    (hwidth : b + b / 1000 ≤ c)
    (_hc_le : c ≤ 2 * b)
    (hp_lt : (p : ℝ) < b)
    (hexp : Real.exp ((3 / 5 : ℝ) * Real.log b) ≤ (c - b) / (2 * p)) :
    (((apInterval b c 2 1).filter (fun x => x % (2 * p) = r)).card : ℝ) ≤
      (5 / 6 : ℝ) * (c - b) / Real.log b := by
  let F := (apInterval b c 2 1).filter (fun x => x % (2 * p) = r)
  have hb0 : 0 ≤ b := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hbc : b ≤ c := by linarith
  have hlog : 0 < Real.log b := Real.log_pos (by linarith)
  by_cases hne : F.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    have hx₀_f := Finset.mem_filter.mp hx₀
    have hx₀_mem := (mem_apInterval_iff b c 2 1 hb0 hc0 x₀).mp hx₀_f.1
    have hx₀_prime : Nat.Prime x₀ := hx₀_mem.1
    have hx₀_gt_b : b < (x₀ : ℝ) := hx₀_mem.2.1
    have hx₀_mod2 : x₀ % 2 = 1 := by exact_mod_cast hx₀_mem.2.2.2
    have hx₀_gt_p : p < x₀ := by exact_mod_cast (hp_lt.trans hx₀_gt_b)
    have hcop_2_x₀ : Nat.Coprime 2 x₀ := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two, Nat.dvd_iff_mod_eq_zero]
      omega
    have hcop_p_x₀ : Nat.Coprime p x₀ := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hdvd
      rcases (Nat.dvd_prime hx₀_prime).mp hdvd with h1 | heq
      · have := hp.two_le; omega
      · omega
    have hcop_2p_x₀ : Nat.Coprime (2 * p) x₀ :=
      Nat.Coprime.mul_left hcop_2_x₀ hcop_p_x₀
    have hp_pos : 0 < p := hp.pos
    have hr_eq : r = x₀ % (2 * p) := hx₀_f.2.symm
    have hcop_2p_r : Nat.Coprime (2 * p) r := by
      rw [hr_eq, Nat.Coprime, Nat.gcd_comm, ← Nat.gcd_rec]
      exact hcop_2p_x₀
    have hr_pos : 0 < r := by
      by_contra hr0
      have hr0' : r = 0 := by omega
      rw [hr0', Nat.coprime_zero_right] at hcop_2p_r
      have := hp.two_le
      omega
    have hr_lt : r < 2 * p := by
      rw [hr_eq]
      exact Nat.mod_lt x₀ (by omega)
    have hF_sub : F ⊆ apInterval b c (2 * p) (r : ℤ) := by
      intro x hx
      have hxf := Finset.mem_filter.mp hx
      have hxm := (mem_apInterval_iff b c 2 1 hb0 hc0 x).mp hxf.1
      rw [mem_apInterval_iff b c (2 * p) (r : ℤ) hb0 hc0]
      refine ⟨hxm.1, hxm.2.1, hxm.2.2.1, ?_⟩
      have hmod_nat : x % (2 * p) = r % (2 * p) := by
        rw [hxf.2, Nat.mod_eq_of_lt hr_lt]
      exact_mod_cast hmod_nat
    have hF_le : (F.card : ℝ) ≤ (apInterval b c (2 * p) (r : ℤ)).card := by
      exact_mod_cast Finset.card_le_card hF_sub
    rcases prime_eq_two_or_three_or_ge_five hp with rfl | rfl | hp5
    · -- Case p = 2: 2 * p = 4, φ(4) = 2
      have hcopZ : Nat.Coprime 4 (r : ℤ).natAbs := by simpa using hcop_2p_r
      have hB := (abs_le.mp (thetaAP_totient_two_all_scales bmor imp
        (q := 4) (a := (r : ℤ)) (by decide) (by decide) (by decide) hcopZ hb)).1
      have hC := (abs_le.mp (thetaAP_totient_two_all_scales bmor imp
        (q := 4) (a := (r : ℤ)) (by decide) (by decide) (by decide) hcopZ (hb.trans hbc))).2
      have hcnt := ut_count_log_le_thetaAP_interval b c 4 (r : ℤ) (by linarith) hbc
      have h4 : ((apInterval b c (2 * 2) (r : ℤ)).card : ℝ) ≤ (5 / 6 : ℝ) * (c - b) / Real.log b := by
        change ((apInterval b c 4 (r : ℤ)).card : ℝ) ≤ _
        rw [le_div_iff₀ hlog]
        linarith
      exact hF_le.trans h4
    · -- Case p = 3: 2 * p = 6, φ(6) = 2
      have hcopZ : Nat.Coprime 6 (r : ℤ).natAbs := by simpa using hcop_2p_r
      have hB := (abs_le.mp (thetaAP_totient_two_all_scales bmor imp
        (q := 6) (a := (r : ℤ)) (by decide) (by decide) (by decide) hcopZ hb)).1
      have hC := (abs_le.mp (thetaAP_totient_two_all_scales bmor imp
        (q := 6) (a := (r : ℤ)) (by decide) (by decide) (by decide) hcopZ (hb.trans hbc))).2
      have hcnt := ut_count_log_le_thetaAP_interval b c 6 (r : ℤ) (by linarith) hbc
      have h6 : ((apInterval b c (2 * 3) (r : ℤ)).card : ℝ) ≤ (5 / 6 : ℝ) * (c - b) / Real.log b := by
        change ((apInterval b c 6 (r : ℤ)).card : ℝ) ≤ _
        rw [le_div_iff₀ hlog]
        linarith
      exact hF_le.trans h6
    · -- Case p ≥ 5: φ(2 * p) = p - 1 ≥ 4, apply Montgomery–Vaughan
      have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
      have hcop_2_p : Nat.Coprime 2 p := by
        rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two, Nat.dvd_iff_mod_eq_zero]
        omega
      have hphi_2p : Nat.totient (2 * p) = p - 1 := by
        rw [Nat.totient_mul hcop_2_p, Nat.totient_two, Nat.totient_prime hp, one_mul]
      have hphi_ge : (4 : ℝ) ≤ (Nat.totient (2 * p) : ℝ) := by
        rw [hphi_2p]
        have : 4 ≤ p - 1 := by omega
        exact_mod_cast this
      have hell_pos : 0 < (3 / 5 : ℝ) * Real.log b := by positivity
      have hk_lt_y : ((2 * p : ℕ) : ℝ) < c - b := by
        have h1 : (1 : ℝ) < Real.exp ((3 / 5 : ℝ) * Real.log b) :=
          Real.one_lt_exp_iff.mpr hell_pos
        have h2 : (1 : ℝ) < (c - b) / (2 * p) := lt_of_lt_of_le h1 hexp
        have hp_pos : (0 : ℝ) < (2 * p : ℝ) := by positivity
        rw [lt_div_iff₀ hp_pos] at h2
        push_cast
        linarith
      have hsub_eq : apInterval b (b + (c - b)) (2 * p) (r : ℤ) = apInterval b c (2 * p) (r : ℤ) := by
        congr 1; ring
      have hmv := mv_short_interval_subset_bound mv b (c - b) ((3 / 5 : ℝ) * Real.log b)
        (2 * p) r F (by linarith) (by linarith) (by positivity) hr_pos hcop_2p_r hk_lt_y
        hell_pos (by push_cast at hexp ⊢; exact hexp) (by rw [hsub_eq]; exact hF_sub)
      have hden_le : 4 * ((3 / 5 : ℝ) * Real.log b) ≤
          (Nat.totient (2 * p) : ℝ) * ((3 / 5 : ℝ) * Real.log b) :=
        mul_le_mul_of_nonneg_right hphi_ge hell_pos.le
      have hdiv_le : 2 * (c - b) / ((Nat.totient (2 * p) : ℝ) * ((3 / 5 : ℝ) * Real.log b)) ≤
          2 * (c - b) / (4 * ((3 / 5 : ℝ) * Real.log b)) :=
        div_le_div_of_nonneg_left (by linarith) (by positivity) hden_le
      have hcalc : 2 * (c - b) / (4 * ((3 / 5 : ℝ) * Real.log b)) =
          (5 / 6 : ℝ) * (c - b) / Real.log b := by ring
      exact le_of_lt (hmv.trans_le (hdiv_le.trans_eq hcalc))
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    change (F.card : ℝ) ≤ _
    rw [hne, Finset.card_empty, Nat.cast_zero]
    positivity

/-! ## Universal Polynomial-vs-Logarithm Envelopes for `n ≥ 35,735` -/

/-- Elementary algebraic bound `(1 + Real.log u / m) ^ m ≤ u` for `1 ≤ u` and `0 < m`. -/
theorem pow_one_add_log_div_le {u : ℝ} (hu : 1 ≤ u) (m : ℕ) (hm : 0 < m) :
    (1 + Real.log u / (m : ℝ)) ^ m ≤ u := by
  have hu_pos : 0 < u := by linarith
  have hlog_nonneg : 0 ≤ Real.log u := Real.log_nonneg hu
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have h1 : 1 + Real.log u / (m : ℝ) ≤ Real.exp (Real.log u / (m : ℝ)) := by
    linarith [Real.add_one_le_exp (Real.log u / (m : ℝ))]
  have h2 : (1 + Real.log u / (m : ℝ)) ^ m ≤ (Real.exp (Real.log u / (m : ℝ))) ^ m :=
    pow_le_pow_left₀ (by positivity) h1 m
  rw [← Real.exp_nat_mul, mul_div_cancel₀ _ hm_pos.ne', Real.exp_log hu_pos] at h2
  exact h2

/-- Convert `b ^ 3 ≤ y ^ 5` into `Real.exp ((3 / 5) * Real.log b) ≤ y` without fractional powers. -/
theorem exp_three_fifths_log_le_of_pow {b y : ℝ} (hb : 0 < b) (hy : 0 ≤ y)
    (hpow : b ^ 3 ≤ y ^ 5) :
    Real.exp ((3 / 5 : ℝ) * Real.log b) ≤ y := by
  have hexp5 : (Real.exp ((3 / 5 : ℝ) * Real.log b)) ^ 5 = b ^ 3 := by
    rw [← Real.exp_nat_mul]
    have hmul : ((5 : ℕ) : ℝ) * ((3 / 5 : ℝ) * Real.log b) = ((3 : ℕ) : ℝ) * Real.log b := by
      push_cast; ring
    rw [hmul, Real.exp_nat_mul, Real.exp_log hb]
  have hle5 : (Real.exp ((3 / 5 : ℝ) * Real.log b)) ^ 5 ≤ y ^ 5 := by
    rw [hexp5]; exact hpow
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le hy (by decide : 5 ≠ 0)).mp hle5

/-- For all `n ≥ 35,735`, `(Real.log n) ^ 3 ≤ (1331 / 32768) * n` and
`(Real.log n) ^ 4 ≤ (14641 / 32768) * n`. -/
theorem log_nat_pow_bounds_ge_35735 {n : ℕ} (hn : 35735 ≤ n) :
    10 < Real.log (n : ℝ) ∧
    (Real.log (n : ℝ)) ^ 3 ≤ (1331 / 32768 : ℝ) * (n : ℝ) ∧
    (Real.log (n : ℝ)) ^ 4 ≤ (14641 / 32768 : ℝ) * (n : ℝ) := by
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  let u : ℝ := (n : ℝ) / 32768
  have hu1 : 1 ≤ u := by dsimp [u]; linarith
  have hlog_u_nonneg : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hn_eq : (n : ℝ) = (2 : ℝ) ^ 15 * u := by dsimp [u]; ring
  have hlog2_lo : (6931471803 / 10000000000 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9; norm_num at h ⊢; exact h
  have hlog2_hi : Real.log 2 < (6931471808 / 10000000000 : ℝ) := by
    have h := Real.log_two_lt_d9; norm_num at h ⊢; exact h
  have hlog_n : Real.log (n : ℝ) = 15 * Real.log 2 + Real.log u := by
    rw [hn_eq, Real.log_mul (by positivity) (by linarith), Real.log_pow]
    push_cast; rfl
  have hlog_gt_10 : 10 < Real.log (n : ℝ) := by linarith
  have hdiv3 : Real.log (n : ℝ) / 11 ≤ 1 + Real.log u / 3 := by linarith
  have hdiv4 : Real.log (n : ℝ) / 11 ≤ 1 + Real.log u / 4 := by linarith
  have hp3 : (Real.log (n : ℝ) / 11) ^ 3 ≤ u :=
    (pow_le_pow_left₀ (by positivity) hdiv3 3).trans (pow_one_add_log_div_le hu1 3 (by decide))
  have hp4 : (Real.log (n : ℝ) / 11) ^ 4 ≤ u :=
    (pow_le_pow_left₀ (by positivity) hdiv4 4).trans (pow_one_add_log_div_le hu1 4 (by decide))
  refine ⟨hlog_gt_10, ?_, ?_⟩
  · dsimp [u] at hp3; linarith
  · dsimp [u] at hp4; linarith

/-- Universal lower and upper bounds on `poolMaximum n` and `Real.log (poolMaximum n)` for `n ≥ 35,735`. -/
theorem poolMaximum_bounds_ge_35735 (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) :
    (222 / 10 : ℝ) * (n : ℝ) ^ 2 < (poolMaximum n : ℝ) ∧
    (283 * 10 ^ 8 : ℝ) < (poolMaximum n : ℝ) ∧
    (poolMaximum n : ℝ) < (n : ℝ) ^ 3 ∧
    (23 : ℝ) < Real.log (poolMaximum n : ℝ) ∧
    Real.log (poolMaximum n : ℝ) < 3 * Real.log (n : ℝ) := by
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hj_ge : (1276990226 : ℝ) ≤ j := by
    dsimp [j]; push_cast; nlinarith
  have hj_pos : 0 < j := by linarith
  have hj_gt1 : 1 < j := by linarith
  have hlog2_lo : (6931471803 / 10000000000 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9; norm_num at h ⊢; exact h
  have hj_pow : (2 : ℝ) ^ 30 < j := lt_of_lt_of_le (by norm_num) hj_ge
  have hlogj : (2079 / 100 : ℝ) < Real.log j := by
    have h := Real.log_lt_log (by positivity) hj_pow
    rw [Real.log_pow] at h; push_cast at h; linarith
  have hll_pow : (2 : ℝ) ^ 17 < (Real.log j) ^ 4 :=
    lt_of_lt_of_le (by norm_num) (pow_le_pow_left₀ (by norm_num) hlogj.le 4)
  have hloglogj : (294 / 100 : ℝ) < Real.log (Real.log j) := by
    have h := Real.log_lt_log (by positivity) hll_pow
    rw [Real.log_pow, Real.log_pow] at h; push_cast at h; linarith
  have hsource : j * (Real.log j + Real.log (Real.log j) - 3 / 2) < (poolMaximum n : ℝ) := by
    have hn2 : 2 ≤ n * n + 1 := by nlinarith
    simpa [j, poolMaximum] using sharp (n * n + 1) hn2
  have hfac : (222 / 10 : ℝ) < Real.log j + Real.log (Real.log j) - 3 / 2 := by linarith
  have hmul_lo := mul_lt_mul_of_pos_left hfac hj_pos
  have hX_sq : (222 / 10 : ℝ) * (n : ℝ) ^ 2 < (poolMaximum n : ℝ) := by
    dsimp [j] at hsource hmul_lo; push_cast at hsource hmul_lo; nlinarith
  have hX_283 : (283 * 10 ^ 8 : ℝ) < (poolMaximum n : ℝ) := by nlinarith
  have hX_23 : (23 : ℝ) < Real.log (poolMaximum n : ℝ) := by
    have hpow : (2 : ℝ) ^ 34 < (poolMaximum n : ℝ) :=
      lt_of_lt_of_le (by norm_num) hX_283.le
    have h := Real.log_lt_log (by positivity) hpow
    rw [Real.log_pow] at h; push_cast at h; linarith
  -- Upper bound `poolMaximum n < n ^ 3`
  have hlog_n_bounds := log_nat_pow_bounds_ge_35735 hn
  have hlogj_lt : Real.log j < (n : ℝ) / 3 := by
    have h1 : Real.log j ≤ Real.log ((n : ℝ) ^ 3) := by
      apply Real.log_le_log hj_pos
      dsimp [j]; push_cast; nlinarith
    rw [Real.log_pow] at h1; push_cast at h1
    have hsq : 100 ≤ (Real.log (n : ℝ)) ^ 2 := by nlinarith [hlog_n_bounds.1]
    have h2 : 100 * Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := by nlinarith [hlog_n_bounds.1, hsq]
    linarith [hlog_n_bounds.2.1]
  have hloglogj_lt : Real.log (Real.log j) < Real.log j := by
    have h := Real.log_le_sub_one_of_pos (Real.log_pos hj_gt1)
    linarith
  have hu := poolMaximum_upper upper n (tail_prime_index_domains (by omega : 2001 ≤ n)).1
  have hX_lt_n3 : (poolMaximum n : ℝ) < (n : ℝ) ^ 3 := by
    have hsum : Real.log j + Real.log (Real.log j) < (2 / 3 : ℝ) * (n : ℝ) := by linarith
    have hprod := mul_lt_mul_of_pos_left hsum hj_pos
    have hlt : (poolMaximum n : ℝ) < j * ((2 / 3 : ℝ) * (n : ℝ)) := lt_trans hu hprod
    dsimp [j] at hlt; push_cast at hlt; nlinarith
  have hlogX_lt : Real.log (poolMaximum n : ℝ) < 3 * Real.log (n : ℝ) := by
    have h := Real.log_lt_log (by linarith) hX_lt_n3
    rw [Real.log_pow] at h; push_cast at h; exact h
  exact ⟨hX_sq, hX_283, hX_lt_n3, hX_23, hlogX_lt⟩

end

end Sude
