import Sude.FWWheelFirstWindowSchedule

/-! Integer arithmetic for the exact conservative first-window floor.
This does not assert growth, crossing, or the frozen mixed recipe. -/
namespace Sude
noncomputable section

/-- The exact nonnegative numerator of the first-window mass coefficient,
with denominator 69780000000000 on the first 118 stages. -/
def fwFirstWindowIntegerRate (j : ℕ) : ℕ := 1119520387869 - 796207000 * j

/-- An integer-only formula for `max 1 (floor(A+1))` on the first band. -/
def fwFirstWindowIntegerCount (j R : ℕ) : ℕ :=
  max 1 ((2 * fwFirstWindowIntegerRate j * R + 69780000000000) / 139560000000000)

/-- Exact numerator identity on the bounded stage domain. -/
theorem fw_first_window_integer_rate_exact {j : ℕ} (hj : j < 118) :
    ((fwFirstWindowIntegerRate j : ℕ) : ℝ) / 69780000000000 =
      (3981035 / 10000000 : ℝ) *
        ((403 / 10000 : ℝ) - 2 * (1 / 69780 : ℝ) * j) := by
  have hle : 796207000 * j ≤ 1119520387869 := by omega
  unfold fwFirstWindowIntegerRate
  rw [Nat.cast_sub hle]
  push_cast
  ring

/-- The exact rational count is safe even before floor feasibility; when
A is negative the natural floor is zero and the maximum retains one. -/
theorem fw_first_window_integer_count_le {j R : ℕ} (hj : j < 118) :
    fwFirstWindowIntegerCount j R ≤ fwFirstWindowT j R + 1 := by
  let A := fwFirstWindowA j R
  let q := (2 * fwFirstWindowIntegerRate j * R + 69780000000000) / 139560000000000
  have hq : (q : ℝ) ≤ A + 1 := by
    have hdiv : (q : ℝ) ≤ ((2 * fwFirstWindowIntegerRate j * R + 69780000000000 : ℕ) : ℝ) / 139560000000000 := by
      exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := 2 * fwFirstWindowIntegerRate j * R + 69780000000000) (n := 139560000000000))
    have hrate := fw_first_window_integer_rate_exact hj
    dsimp [A, fwFirstWindowA]
    push_cast at hdiv
    nlinarith
  have hq' : q ≤ fwFirstWindowT j R + 1 := by
    by_cases hA : 0 ≤ A
    · have hf := Nat.le_floor hq
      rw [Nat.floor_add_one hA] at hf
      exact hf
    · have hq0 : q = 0 := by
        have hqR : (q : ℝ) < 1 := by linarith
        have : q < 1 := by exact_mod_cast hqR
        omega
      rw [hq0]
      omega
  unfold fwFirstWindowIntegerCount
  exact max_le (by omega) hq'

end
end Sude
