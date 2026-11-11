import Sude.PrefixCount

/-! Prove FPF endpoint containment from an existing published index bound.
This avoids a separate odd-prime prefix-count certificate for the L and T
endpoint bounds; it does not certify the FPF pair populations. -/
namespace Sude
noncomputable section

/-- A rational lower bound for log(15/8), using the library's proved
upper bound for e and the exact exponential addition law. -/
theorem half_lt_log_fifteen_eighths : (1 / 2 : ℝ) < Real.log (15 / 8) := by
  have hpos : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
  have hsq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  have hexp : Real.exp (1 / 2 : ℝ) < (15 / 8 : ℝ) := by
    have he := Real.exp_one_lt_three
    nlinarith
  exact (Real.lt_log_iff_exp_lt (by norm_num)).2 hexp

/-- A uniform logarithmic index bound for the lower-controller domain. -/
theorem finitePrefix_log_index_gt_fifteen {n : ℕ} (hn : 2000 ≤ n) :
    (15 : ℝ) < Real.log ((n * n + 1 : ℕ) : ℝ) := by
  have hn' : (2000 : ℝ) ≤ n := by exact_mod_cast hn
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hj : (4000001 : ℝ) ≤ j := by
    dsimp [j]
    push_cast
    nlinarith
  have hthreshold : (15 / 8 : ℝ) * 2 ^ 21 ≤ j := by norm_num at *; linarith
  have hlogThreshold : (15 : ℝ) < Real.log ((15 / 8 : ℝ) * 2 ^ 21) := by
    rw [Real.log_mul (by norm_num : (15 / 8 : ℝ) ≠ 0) (by positivity : (2 : ℝ) ^ 21 ≠ 0),
      Real.log_pow]
    have h1 := half_lt_log_fifteen_eighths
    have h2 := Real.log_two_gt_d9
    norm_num at h1 h2 ⊢
    linarith
  exact lt_of_lt_of_le hlogThreshold (Real.log_le_log (by positivity) hthreshold)

/-- The L-family upper endpoint is strictly below the actual pool maximum
for every n≥2000, using the already-declared RS lower-index estimate. -/
theorem finitePrefix_L_below_poolMaximum (lower : RSIndexLower) {n : ℕ}
    (hn : 2000 ≤ n) : 60000000 < poolMaximum n := by
  have hn' : (2000 : ℝ) ≤ n := by exact_mod_cast hn
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hj : (4000001 : ℝ) ≤ j := by
    dsimp [j]
    push_cast
    nlinarith
  have hlog : (15 : ℝ) < Real.log j := finitePrefix_log_index_gt_fifteen hn
  have hlower : j * Real.log j < (poolMaximum n : ℝ) := poolMaximum_lower lower n
  have hmax : (60000000 : ℝ) < (poolMaximum n : ℝ) := by nlinarith
  exact_mod_cast hmax

/-- C27's selected endpoints are at most 74 million, even though its
source sieve runs through 95 million. The endpoint bound, not the sieve
bound, is what pool membership requires. -/
theorem finitePrefix_C27_below_poolMaximum (lower : RSIndexLower) {n : ℕ}
    (hn : 2400 ≤ n) : 74000000 < poolMaximum n := by
  have hn' : (2400 : ℝ) ≤ n := by exact_mod_cast hn
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hj : (5760001 : ℝ) ≤ j := by
    dsimp [j]
    push_cast
    nlinarith
  have hlog : (15 : ℝ) < Real.log j := finitePrefix_log_index_gt_fifteen (by omega)
  have hlower : j * Real.log j < (poolMaximum n : ℝ) := poolMaximum_lower lower n
  have hmax : (74000000 : ℝ) < (poolMaximum n : ℝ) := by nlinarith
  exact_mod_cast hmax

/-- The T-family upper endpoint is below the actual pool maximum for all
n≥10000, without evaluating the 1.8-billion prime prefix. -/
theorem finitePrefix_T_below_poolMaximum (lower : RSIndexLower) {n : ℕ}
    (hn : 10000 ≤ n) : 1800000000 < poolMaximum n := by
  have hn' : (10000 : ℝ) ≤ n := by exact_mod_cast hn
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hj : (100000001 : ℝ) ≤ j := by
    dsimp [j]
    push_cast
    nlinarith
  have hthreshold : (2 : ℝ) ^ 26 ≤ j := by norm_num at *; linarith
  have hlogThreshold : (18 : ℝ) < Real.log ((2 : ℝ) ^ 26) := by
    rw [Real.log_pow]
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hlog : (18 : ℝ) < Real.log j := by
    exact lt_of_lt_of_le hlogThreshold (Real.log_le_log (by positivity) hthreshold)
  have hlower : j * Real.log j < (poolMaximum n : ℝ) := poolMaximum_lower lower n
  have hmax : (1800000000 : ℝ) < (poolMaximum n : ℝ) := by nlinarith
  exact_mod_cast hmax

theorem finitePrefix_L_prime_in_pool (lower : RSIndexLower) {n p : ℕ}
    (hn : 2000 ≤ n) (hp : Nat.Prime p) (hne : p ≠ 2) (hpmax : p ≤ 60000000) :
    p ∈ pool n :=
  prime_mem_pool_of_le_max hp hne (le_trans hpmax (finitePrefix_L_below_poolMaximum lower hn).le)

theorem finitePrefix_T_prime_in_pool (lower : RSIndexLower) {n p : ℕ}
    (hn : 10000 ≤ n) (hp : Nat.Prime p) (hne : p ≠ 2) (hpmax : p ≤ 1800000000) :
    p ∈ pool n :=
  prime_mem_pool_of_le_max hp hne (le_trans hpmax (finitePrefix_T_below_poolMaximum lower hn).le)

theorem finitePrefix_C27_prime_in_pool (lower : RSIndexLower) {n p : ℕ}
    (hn : 2400 ≤ n) (hp : Nat.Prime p) (hne : p ≠ 2) (hpmax : p ≤ 74000000) :
    p ∈ pool n :=
  prime_mem_pool_of_le_max hp hne (le_trans hpmax (finitePrefix_C27_below_poolMaximum lower hn).le)

end
end Sude
