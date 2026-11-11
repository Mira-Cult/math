import Sude.PrimeIndex

/-! A source-faithful explicit sharp index premise and its FW consequence. -/
namespace Sude
noncomputable section

/-- Rosser--Schoenfeld (1962), Theorem 3, (3.10), printed p. 69:
the lower bound for the one-based prime index `j ≥ 2`. This is an
explicit published theorem hypothesis, not a Lean axiom or controller. -/
def RSIndexLowerSharp : Prop := ∀ j : ℕ, 2 ≤ j →
  (j : ℝ) * (Real.log (j : ℝ) + Real.log (Real.log (j : ℝ)) - 3 / 2) <
    (primeOneBased j : ℝ)

/-- The explicit RS sharp lower-index estimate implies a simpler lower
bound for the maximum of the exact prescribed pool in the FW domain. -/
theorem fw_poolMaximum_gt_twenty_one_sq (sharp : RSIndexLowerSharp) {n : ℕ}
    (hn : 19485 ≤ n) : (21 : ℝ) * (n : ℝ) ^ 2 < poolMaximum n := by
  have hnreal : (19485 : ℝ) ≤ n := by exact_mod_cast hn
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hj : (379665226 : ℝ) ≤ j := by
    dsimp [j]
    push_cast
    nlinarith
  have hjpos : 0 < j := by linarith
  have hj2 : (2 : ℝ) ^ 57 < j ^ 2 := by
    norm_num
    nlinarith
  have hlogj : (79 / 4 : ℝ) < Real.log j := by
    have h := Real.log_lt_log (show (0 : ℝ) < (2 : ℝ) ^ 57 by positivity) hj2
    rw [Real.log_pow, Real.log_pow] at h
    have hlog2 := Real.log_two_gt_d9
    norm_num at h hlog2 ⊢
    linarith
  have hloglogj : (11 / 4 : ℝ) < Real.log (Real.log j) := by
    have h := Real.log_lt_log (show (0 : ℝ) < 16 by norm_num) (show (16 : ℝ) < Real.log j by linarith)
    have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [← show (2 : ℝ) ^ 4 = 16 by norm_num, Real.log_pow]
      norm_num
    rw [hlog16] at h
    have hlog2 := Real.log_two_gt_d9
    norm_num at h hlog2 ⊢
    linarith
  have hfactor : (21 : ℝ) < Real.log j + Real.log (Real.log j) - 3 / 2 := by linarith
  have hsource : j * (Real.log j + Real.log (Real.log j) - 3 / 2) <
      (poolMaximum n : ℝ) := by
    have hnpos : 0 < n := by omega
    have hn2 : 0 < n * n := Nat.mul_pos hnpos hnpos
    simpa [j, poolMaximum] using sharp (n * n + 1) (by omega)
  have hscaled : 21 * j < j * (Real.log j + Real.log (Real.log j) - 3 / 2) := by
    nlinarith [mul_lt_mul_of_pos_right hfactor hjpos]
  have hscale : 21 * j < (poolMaximum n : ℝ) := lt_trans hscaled hsource
  dsimp [j] at hscale
  push_cast at hscale
  nlinarith

end
end Sude
