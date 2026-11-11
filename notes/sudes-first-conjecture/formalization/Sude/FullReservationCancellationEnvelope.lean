import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! A real-algebra envelope for a supplied exact full-reservation
cancellation identity. No physical, mean, line or diagonal bound is asserted. -/
namespace Sude
noncomputable section

/-- Bound the signed cancellation using supplied absolute budgets. The two
cases of `q` are explicit, and no interpretation of the variables is assumed. -/
theorem full_reservation_cancellation_envelope
    (n r q b N A O D μu μ Amax Omax Dmax : ℝ)
    (hn : 19485 ≤ n) (hb : 0 ≤ b) (hN : 0 < N)
    (hrq : 0 ≤ r + q ∧ r + q ≤ n) (hq : q = 0 ∨ q = 2)
    (hAmax : 0 ≤ Amax) (hOmax : 0 ≤ Omax) (hDmax : 0 ≤ Dmax)
    (hA : |A| ≤ Amax) (hO : |O| ≤ Omax) (hD : |D| ≤ Dmax)
    (hid : 12 * A + (n - r - q) * (μu - μ) =
      (12 * A / N) * ((n + 8) * q - b - 8 * n) - (n - r - q) * (O + D) / N) :
    |12 * A + (n - r - q) * (μu - μ)| ≤
      (12 * Amax * (8 * n + b) + (n - r) * (Omax + Dmax)) / N := by
  have hq0 : 0 ≤ q := by rcases hq with hq | hq <;> linarith
  have hk0 : 0 ≤ n - r - q := by linarith [hrq.2]
  have hkr : n - r - q ≤ n - r := by linarith
  have hcoeff : |(n + 8) * q - b - 8 * n| ≤ 8 * n + b := by
    rcases hq with hq | hq
    · rw [hq]
      apply abs_le.mpr
      constructor <;> linarith
    · rw [hq]
      apply abs_le.mpr
      constructor <;> linarith
  have hbudget : |O + D| ≤ Omax + Dmax :=
    (abs_add_le O D).trans (add_le_add hO hD)
  have hprodA : |A| * |(n + 8) * q - b - 8 * n| ≤ Amax * (8 * n + b) :=
    mul_le_mul hA hcoeff (abs_nonneg _) hAmax
  have hprodR : (n - r - q) * |O + D| ≤ (n - r) * (Omax + Dmax) := by
    calc
      _ ≤ (n - r - q) * (Omax + Dmax) := mul_le_mul_of_nonneg_left hbudget hk0
      _ ≤ (n - r) * (Omax + Dmax) := mul_le_mul_of_nonneg_right hkr (add_nonneg hOmax hDmax)
  have htermA : |(12 * A / N) * ((n + 8) * q - b - 8 * n)| ≤
      12 * Amax * (8 * n + b) / N := by
    have heq : |(12 * A / N) * ((n + 8) * q - b - 8 * n)| =
        (12 * (|A| * |(n + 8) * q - b - 8 * n|)) / N := by
      rw [abs_mul, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 12), abs_of_pos hN]
      ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ hN.le
    nlinarith
  have htermR : |(n - r - q) * (O + D) / N| ≤
      (n - r) * (Omax + Dmax) / N := by
    rw [abs_div, abs_mul, abs_of_nonneg hk0, abs_of_pos hN]
    exact div_le_div_of_nonneg_right hprodR hN.le
  rw [hid]
  calc
    |(12 * A / N) * ((n + 8) * q - b - 8 * n) - (n - r - q) * (O + D) / N| ≤
        |(12 * A / N) * ((n + 8) * q - b - 8 * n)| + |(n - r - q) * (O + D) / N| :=
          abs_sub _ _
    _ ≤ 12 * Amax * (8 * n + b) / N + (n - r) * (Omax + Dmax) / N :=
      add_le_add htermA htermR
    _ = (12 * Amax * (8 * n + b) + (n - r) * (Omax + Dmax)) / N := by ring

end
end Sude
