import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
The signed scalar cancellation used in PB12 and CY8.  This module does not
construct the reserved family or the unused pool: their total deviations,
counts, and physical interpretation must be supplied separately.
-/

namespace Sude

/-- The family mean term and its unused-pool correction combine exactly;
the signed deviation of all other reservations remains visible. -/
theorem signed_family_unused_mean_cancellation_real
    (n d r q br N k A other : ℝ)
    (hN : N = n ^ 2 - (r * (n + 8) + br))
    (hk : k = n - r - q) (hNne : N ≠ 0) :
    2 * d * A - k * (2 * (d * (n + 8)) * A + other) / N =
      (2 * d * A / N) * ((n + 8) * q - br - 8 * n) - k * other / N := by
  subst N
  subst k
  field_simp
  ring

/-- Natural reservation counts, with all signed differences taken in `ℝ`.
The strict count bound supplies a positive denominator; the line-count bound
justifies casting the two natural subtractions. -/
theorem signed_family_unused_mean_cancellation
    (n d r q br : ℕ) (A other : ℝ)
    (hreserved : r * (n + 8) + br < n * n)
    (hline : r + q ≤ n) :
    let N : ℝ := (n * n - (r * (n + 8) + br) : ℕ)
    let k : ℝ := (n - r - q : ℕ)
    2 * (d : ℝ) * A - k * (2 * (d : ℝ) * ((n : ℝ) + 8) * A + other) / N =
      (2 * (d : ℝ) * A / N) * (((n : ℝ) + 8) * (q : ℝ) - br - 8 * n) -
        k * other / N := by
  dsimp only
  have hB : r * (n + 8) + br ≤ n * n := Nat.le_of_lt hreserved
  have hr : r ≤ n := by omega
  have hq : q ≤ n - r := by omega
  have hN : ((n * n - (r * (n + 8) + br) : ℕ) : ℝ) =
      (n : ℝ) ^ 2 - ((r : ℝ) * ((n : ℝ) + 8) + (br : ℝ)) := by
    rw [Nat.cast_sub hB]
    push_cast
    ring
  have hk : ((n - r - q : ℕ) : ℝ) = (n : ℝ) - (r : ℝ) - (q : ℝ) := by
    rw [Nat.cast_sub hq, Nat.cast_sub hr]
  have hNne : ((n * n - (r * (n + 8) + br) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hreserved))
  simpa only [mul_assoc] using signed_family_unused_mean_cancellation_real n d r q br
    ((n * n - (r * (n + 8) + br) : ℕ) : ℝ) ((n - r - q : ℕ) : ℝ)
    A other hN hk hNne

end Sude
