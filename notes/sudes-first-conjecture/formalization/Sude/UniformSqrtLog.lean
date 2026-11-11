import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace Sude

/-- A pointwise square-root/logarithm majorant becomes uniform on `[2,X]`
when `log X ≥ 24`. No assertion about any particular error term is used. -/
theorem sqrt_log_ratio_le {t X : ℝ} (ht : 2 ≤ t) (htX : t ≤ X)
    (hX : 24 ≤ Real.log X) :
    Real.sqrt t / Real.log t ≤ Real.sqrt X / Real.log X := by
  have htpos : 0 < t := by linarith
  have hXpos : 0 < X := by linarith
  have hlt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlX : 0 < Real.log X := by linarith
  have hsqt : 0 < Real.sqrt t := Real.sqrt_pos.2 htpos
  have hsqX : 0 < Real.sqrt X := Real.sqrt_pos.2 hXpos
  have hexpX : Real.exp 2 ≤ X := by
    have h := Real.exp_le_exp.mpr (show (2 : ℝ) ≤ Real.log X by linarith)
    simpa [Real.exp_log hXpos] using h
  have hrecip {a b : ℝ} (ha : 0 < Real.log a) (hb : 0 < Real.log b)
      (hsqa : 0 < Real.sqrt a) (hsqb : 0 < Real.sqrt b)
      (h : Real.log b / Real.sqrt b ≤ Real.log a / Real.sqrt a) :
      Real.sqrt a / Real.log a ≤ Real.sqrt b / Real.log b := by
    have h' := (inv_le_inv₀ (div_pos ha hsqa) (div_pos hb hsqb)).2 h
    simpa only [inv_div] using h'
  by_cases hlarge : Real.exp 2 ≤ t
  · apply hrecip hlt hlX hsqt hsqX
    exact Real.log_div_sqrt_antitoneOn hlarge hexpX htX
  · have htbound : t ≤ 9 := by
      have he : Real.exp (1 : ℝ) < 3 := by linarith [Real.exp_one_lt_d9]
      have hsq : Real.exp 2 = Real.exp 1 ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_num
      have hp : 0 < Real.exp (1 : ℝ) := Real.exp_pos _
      nlinarith
    have hsqtbound : Real.sqrt t ≤ 3 := by
      have hs := Real.sq_sqrt (le_of_lt htpos)
      nlinarith [Real.sqrt_nonneg t]
    have hlogbound : (1 / 2 : ℝ) ≤ Real.log t := by
      have h := Real.log_le_log (show (0 : ℝ) < 2 by norm_num) ht
      linarith [Real.log_two_gt_d9]
    have hsmall : Real.sqrt t / Real.log t ≤ 6 := by
      apply (div_le_iff₀ hlt).2
      nlinarith
    have hexp12 : 144 ≤ Real.exp 12 := by
      have he : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
      have hp : 0 ≤ Real.exp (3 : ℝ) := Real.exp_nonneg _
      have hpow : (4 : ℝ)^4 ≤ Real.exp 3 ^ 4 := pow_le_pow_left₀ (by norm_num) he _
      have hid : Real.exp 12 = Real.exp 3 ^ 4 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [hid]
      norm_num at hpow ⊢
      linarith
    have hsqexp : Real.sqrt (Real.exp 24) = Real.exp 12 := by
      convert (Real.exp_half (24 : ℝ)).symm using 1; norm_num
    have hbig : 6 ≤ Real.sqrt X / Real.log X := by
      have h24 : Real.exp 24 ≤ X := by
        have h := Real.exp_le_exp.mpr hX
        simpa [Real.exp_log hXpos] using h
      have hanti := Real.log_div_sqrt_antitoneOn (show Real.exp 2 ≤ Real.exp 24 by
        exact Real.exp_le_exp.mpr (by norm_num)) (show Real.exp 2 ≤ X from hexpX) h24
      have hratio : Real.log X / Real.sqrt X ≤ 1 / 6 := by
        have : Real.log (Real.exp 24) / Real.sqrt (Real.exp 24) ≤ (1 / 6 : ℝ) := by
          rw [Real.log_exp, hsqexp]
          apply (div_le_iff₀ (Real.exp_pos 12)).2
          nlinarith
        exact hanti.trans this
      apply (le_div_iff₀ hlX).2
      have := (div_le_iff₀ hsqX).1 hratio
      nlinarith
    exact hsmall.trans hbig

/-- Transport an explicit pointwise error bound to a common endpoint. -/
theorem uniform_sqrt_log_error {E : ℝ → ℝ} {C X : ℝ}
    (hC : 0 ≤ C) (hX : 24 ≤ Real.log X)
    (hE : ∀ t, 2 ≤ t → t ≤ X → |E t| ≤ C * (Real.sqrt t / Real.log t)) :
    ∀ t, 2 ≤ t → t ≤ X → |E t| ≤ C * (Real.sqrt X / Real.log X) := by
  intro t ht htX
  exact (hE t ht htX).trans (mul_le_mul_of_nonneg_left (sqrt_log_ratio_le ht htX hX) hC)

end Sude
