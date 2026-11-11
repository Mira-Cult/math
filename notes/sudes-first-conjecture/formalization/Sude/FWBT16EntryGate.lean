import Sude.BTGrowingIteration
import Mathlib.Analysis.Complex.ExponentialBounds
/-! Conditional numerical entry gate for a fixed-mass g=2 BT stage.
The radius is supplied; this file does not establish a trace, crossing,
pair budget or the imported Brun--Titchmarsh hypothesis. -/
namespace Sude
noncomputable section

theorem fw_bt_exp_16_upper : Real.exp 16 < (8886111 : ℝ) := by
  have h : Real.exp 1 ≤ (2.7182818286 : ℝ) := Real.exp_one_lt_d9.le
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le h 16
  have hid : Real.exp 1 ^ (16 : ℕ) = Real.exp 16 := by rw [Real.exp_one_pow]; norm_num
  rw [hid] at hp
  norm_num at hp ⊢
  linarith

theorem fw_bt16_fixed_mass_gate {R : ℕ} {m : ℝ}
    (hm : (3257 / 100000 : ℝ) ≤ m) (hR : 171331843 ≤ R) :
    Real.exp 16 ≤ 4 * ((3981035 / 10000000 : ℝ) * m * R - 1 / 2) := by
  have hRn : (171331843 : ℝ) ≤ R := by exact_mod_cast hR
  have hr : (0 : ℝ) ≤ R := by positivity
  have hmul := mul_le_mul hm hRn (by norm_num : (0 : ℝ) ≤ 171331843) (by positivity : 0 ≤ m)
  have hexp := fw_bt_exp_16_upper
  nlinarith

/-- The same bound remains valid when the real BT width is capped at the
supplied actual radius. Here `8*(eta*m*R-1/2)` is the source width for
lambda=16, g=2, phi(2)=1 and r=1. -/
theorem fw_bt16_fixed_mass_capped_gate {R : ℕ} {m : ℝ}
    (hm : (3257 / 100000 : ℝ) ≤ m) (hR : 171331843 ≤ R) :
    let D := 8 * ((3981035 / 10000000 : ℝ) * m * R - 1 / 2)
    Real.exp 16 ≤ min (R : ℝ) D / 2 ∧ 2 < D := by
  dsimp only
  have hgate := fw_bt16_fixed_mass_gate hm hR
  have hexp := fw_bt_exp_16_upper
  have hexplower := Real.add_one_le_exp (16 : ℝ)
  have hRn : (171331843 : ℝ) ≤ R := by exact_mod_cast hR
  constructor
  · have hRpaid : 2 * Real.exp 16 ≤ (R : ℝ) := by linarith
    have hDpaid : 2 * Real.exp 16 ≤
        8 * ((3981035 / 10000000 : ℝ) * m * R - 1 / 2) := by linarith
    have hmin := le_min hRpaid hDpaid
    linarith
  · linarith

end
end Sude
