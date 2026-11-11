import Sude.FinitePrefixPoolBound

/-! FW2's finite seed bound follows from the published index estimate. -/
namespace Sude

/-- In the FW range, the actual maximum of the prescribed pool is more
than four times the finite seed-sieve bound `2^30`. -/
theorem fw_poolMaximum_gt_four_seed (lower : RSIndexLower) {n : ℕ}
    (hn : 19485 ≤ n) : 4 * 2 ^ 30 < poolMaximum n := by
  have hn' : (19485 : ℝ) ≤ n := by exact_mod_cast hn
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hj : (379665226 : ℝ) ≤ j := by
    dsimp [j]
    push_cast
    nlinarith
  have hlog : (15 : ℝ) < Real.log j :=
    finitePrefix_log_index_gt_fifteen (by omega)
  have hlower : j * Real.log j < (poolMaximum n : ℝ) := poolMaximum_lower lower n
  have hmax : (4 * 2 ^ 30 : ℝ) < (poolMaximum n : ℝ) := by nlinarith
  exact_mod_cast hmax

end Sude
