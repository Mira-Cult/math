import Sude.FWFirstWindowCertifiedRadius
import Sude.FWWindowCutoffLower

/-! An elementary per-step lower bound for the conservative first-window
certified-radius recurrence. It does not assert crossing or a source recipe. -/
namespace Sude
noncomputable section

/-- All 118 conservative mass coefficients dominate 1/69. -/
theorem fw_first_window_coefficient_lower {j : ℕ} (hj : j < 118) :
    (1 / 69 : ℝ) ≤ (3981035 / 10000000 : ℝ) *
      ((403 / 10000 : ℝ) - 2 * (1 / 69780 : ℝ) * j) := by
  have hj' : (j : ℝ) ≤ 117 := by exact_mod_cast (show j ≤ 117 by omega)
  linarith

/-- The exact floor dominates the convenient rational lower count. -/
theorem fw_first_window_floor_coarse {j R : ℕ} (hj : j < 118) :
    (2 * R + 69) / 138 ≤ fwFirstWindowT j R + 1 := by
  let A := fwFirstWindowA j R
  let q := (2 * R + 69) / 138
  have hcoeff := fw_first_window_coefficient_lower hj
  have hR : (0 : ℝ) ≤ R := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcoeff hR
  have hq : (q : ℝ) ≤ A + 1 := by
    have hdiv : (q : ℝ) ≤ ((2 * R + 69 : ℕ) : ℝ) / 138 := by
      exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := 2 * R + 69) (n := 138))
    dsimp [A, fwFirstWindowA] at *
    push_cast at hdiv
    linarith
  by_cases hA : 0 ≤ A
  · have hf := Nat.le_floor hq
    rw [Nat.floor_add_one hA] at hf
    exact hf
  · have hq0 : q = 0 := by
      have hq' : (q : ℝ) < 1 := by linarith
      have : q < 1 := by exact_mod_cast hq'
      omega
    change q ≤ fwFirstWindowT j R + 1
    rw [hq0]
    omega

/-- A wheel-window lower bound turns the real floor into a purely integer
radius increment. The window inequality is supplied explicitly here. -/
theorem fw_first_window_coarse_cutoff_of_window {j R : ℕ} (hj : j < 118)
    (hR : 32 ≤ R)
    (hwindow : fwFirstWindowT j R + 1 ≤
      fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015)
        (fwFirstWindowT j R) (Nat.totient_pos.mpr (by decide))) :
    2 * max 1 ((2 * R + 69) / 138) ≤ fwFirstWindowCutoff j R := by
  have hq := fw_first_window_floor_coarse (R := R) hj
  have hqcap : (2 * R + 69) / 138 ≤ R / 2 := by omega
  have honecap : 1 ≤ R / 2 := by omega
  have hqwind : (2 * R + 69) / 138 ≤
      fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015)
        (fwFirstWindowT j R) (Nat.totient_pos.mpr (by decide)) := le_trans hq hwindow
  have hwind : 1 ≤ fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015)
      (fwFirstWindowT j R) (Nat.totient_pos.mpr (by decide)) := by omega
  have hmin : max 1 ((2 * R + 69) / 138) ≤ min
      (fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015)
        (fwFirstWindowT j R) (Nat.totient_pos.mpr (by decide))) (R / 2) :=
    le_min (max_le hwind hqwind) (max_le honecap hqcap)
  exact Nat.mul_le_mul_left 2 hmin

/-- The cutoff always pays the coarse integer increment. -/
theorem fw_first_window_coarse_cutoff {j R : ℕ} (hj : j < 118) (hR : 32 ≤ R) :
    2 * max 1 ((2 * R + 69) / 138) ≤ fwFirstWindowCutoff j R :=
  fw_first_window_coarse_cutoff_of_window hj hR
    (fw_wheel_cutoff_ge_succ 15015 (fwFirstWindowT j R) (by decide))

end
end Sude
