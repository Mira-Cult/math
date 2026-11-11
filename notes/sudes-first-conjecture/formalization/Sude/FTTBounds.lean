import Sude.FTTTargets
import Mathlib.Data.Real.Basic

/-! Exact arithmetic-to-real translations for the FTT row radius. -/
namespace Sude.Lucas

theorem absDiff_cast_real (a b : ℕ) : ((absDiff a b : ℕ) : ℝ) = |(a : ℝ) - b| := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (absDiff_cast a b)
  simpa only [Int.cast_natCast, Int.cast_abs, Int.cast_sub] using h

/-- The integer radius gate in a target row implies the actual real radius,
including the division by a strictly positive order. -/
theorem integer_radius_implies_real {n X T z : ℕ} (hn : 0 < n)
    (h : 1000 * absDiff (n * z) T ≤ n * X) :
    |(z : ℝ) - (T : ℝ) / n| ≤ (X : ℝ) / 1000 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcast : (1000 : ℝ) * (absDiff (n * z) T : ℝ) ≤ (n : ℝ) * X := by
    exact_mod_cast h
  rw [absDiff_cast_real] at hcast
  have hid : |(n : ℝ) * z - T| = n * |(z : ℝ) - (T : ℝ) / n| := by
    have heq : (n : ℝ) * ((z : ℝ) - (T : ℝ) / n) = (n : ℝ) * z - T := by
      field_simp
    rw [← heq, abs_mul, abs_of_pos hnR]
  rw [Nat.cast_mul, hid] at hcast
  nlinarith

/-- Every target in a valid data row is within the stated real radius of
that row's literal mean. Pool identification is a separate premise. -/
theorem targetRowValid_real_radius {r : TargetRow} (h : TargetRowValid r) :
    |(r.common : ℝ) - (r.total : ℝ) / r.order| ≤ (r.maxEntry : ℝ) / 1000 ∧
    |(r.penultimate : ℝ) - (r.total : ℝ) / r.order| ≤ (r.maxEntry : ℝ) / 1000 ∧
    |(r.last : ℝ) - (r.total : ℝ) / r.order| ≤ (r.maxEntry : ℝ) / 1000 := by
  rcases h with ⟨_, _, _, hn, _, _, _, _, _, _, _, _, _, _, _, hq, hp, hr, _, _⟩
  have hn' : 0 < r.order := by omega
  exact ⟨integer_radius_implies_real hn' hq, integer_radius_implies_real hn' hp,
    integer_radius_implies_real hn' hr⟩

end Sude.Lucas
