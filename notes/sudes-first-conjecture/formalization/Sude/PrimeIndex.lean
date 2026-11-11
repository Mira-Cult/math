import Sude.Statement
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Source-faithful prime-index imports and pool translation

Rosser--Schoenfeld (1962), printed p. 69, (3.11)--(3.13). These are
hypotheses, not Lean proofs of the published estimates. See
`import-map.json` for the source pin and application ledger. The translations
below do not assume a controller or a square exists.
-/

namespace Sude

noncomputable section

/-- One-based prime enumeration, as in Rosser--Schoenfeld. Only positive
indices occur in the imported estimates. -/
def primeOneBased (j : ℕ) : ℕ := Nat.nth Nat.Prime (j - 1)

@[simp] theorem primeOneBased_succ (k : ℕ) :
    primeOneBased (k + 1) = Nat.nth Nat.Prime k := by
  simp [primeOneBased]

@[simp] theorem primeOneBased_one : primeOneBased 1 = 2 := by
  simp [primeOneBased]

@[simp] theorem primeOneBased_two : primeOneBased 2 = 3 := by
  simp [primeOneBased]

/-- The prescribed pool's largest prime for positive orders. -/
def poolMaximum (n : ℕ) : ℕ := Nat.nth Nat.Prime (n * n)

/-- Exact published hypotheses; each translation takes only the field it uses. -/
def RSIndexUpperSharp : Prop := ∀ j : ℕ, 20 ≤ j →
  (primeOneBased j : ℝ) < (j : ℝ) *
    (Real.log (j : ℝ) + Real.log (Real.log (j : ℝ)) - 1 / 2)

def RSIndexLower : Prop := ∀ j : ℕ, 1 ≤ j →
  (j : ℝ) * Real.log (j : ℝ) < (primeOneBased j : ℝ)

def RSIndexUpper : Prop := ∀ j : ℕ, 6 ≤ j →
  (primeOneBased j : ℝ) < (j : ℝ) *
    (Real.log (j : ℝ) + Real.log (Real.log (j : ℝ)))

/-- Exact source statements, with natural logarithms and the one-based
prime convention. These are explicit external hypotheses, not axioms. -/
structure RSIndexImports : Prop where
  upper_sharp : RSIndexUpperSharp
  lower : RSIndexLower
  upper : RSIndexUpper

theorem poolMaximum_prime (n : ℕ) : Nat.Prime (poolMaximum n) := by
  exact Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (n * n)

/-- The value `poolMaximum` is actually in the prescribed pool when n > 0. -/
theorem poolMaximum_mem {n : ℕ} (hn : 0 < n) : poolMaximum n ∈ pool n := by
  have hpos : 0 < n * n := Nat.mul_pos hn hn
  refine ⟨⟨n * n - 1, by omega⟩, ?_⟩
  simp only [oddPrime, poolMaximum]
  congr 1
  omega

/-- Every prescribed input prime is at most the proposed maximum. -/
theorem pool_le_poolMaximum {n p : ℕ} (hp : p ∈ pool n) : p ≤ poolMaximum n := by
  obtain ⟨i, rfl⟩ := hp
  apply (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
  omega

/-- A prime is in the exact pool as soon as it is at most the largest
    prescribed entry and is not the omitted prime 2. -/
theorem prime_mem_pool_of_le_max {n p : ℕ} (hp : Nat.Prime p)
    (hne : p ≠ 2) (hmax : p ≤ poolMaximum n) : p ∈ pool n := by
  have hrange : p ∈ Set.range (Nat.nth Nat.Prime) := Nat.subset_range_nth hp
  obtain ⟨k, hk⟩ := hrange
  have hkpos : 0 < k := by
    by_contra h
    have hkzero : k = 0 := by omega
    subst k
    simp only [Nat.nth_prime_zero_eq_two] at hk
    exact hne hk.symm
  have hkle : k ≤ n * n := by
    apply (Nat.nth_le_nth Nat.infinite_setOfPred_prime).mp
    simpa only [hk, poolMaximum] using hmax
  refine ⟨⟨k - 1, by omega⟩, ?_⟩
  change Nat.nth Nat.Prime (k - 1 + 1) = p
  simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hk

/-- The lower source estimate at exactly the last pool index. -/
theorem poolMaximum_lower (lower : RSIndexLower) (n : ℕ) :
    ((n * n + 1 : ℕ) : ℝ) * Real.log ((n * n + 1 : ℕ) : ℝ) <
      (poolMaximum n : ℝ) := by
  simpa [poolMaximum] using lower (n * n + 1) (by omega)

/-- The lower-index logarithmic envelope used in S18.11, with the
    base-two variable eliminated: v log 2 = log n. -/
theorem poolMaximum_log_lower (lower : RSIndexLower) (n : ℕ) (hn : 2 ≤ n) :
    2 * Real.log (n : ℝ) + Real.log (2 * Real.log (n : ℝ)) <
      Real.log (poolMaximum n : ℝ) := by
  have hnreal : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  let a : ℝ := n
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hsq : 0 < a ^ 2 := by
    dsimp [a]
    positivity
  have hj : a ^ 2 < j := by
    dsimp [a, j]
    push_cast
    nlinarith [sq_nonneg (n : ℝ)]
  have hlogj : 2 * Real.log a < Real.log j := by
    have h := Real.log_lt_log hsq hj
    simpa [Real.log_pow] using h
  have hlogpos : 0 < 2 * Real.log a := by
    dsimp [a]
    positivity
  have hjpos : 0 < j := lt_trans hsq hj
  have hproduct : a ^ 2 * (2 * Real.log a) < j * Real.log j :=
    mul_lt_mul hj (le_of_lt hlogj) hlogpos (le_of_lt hjpos)
  have hlower : j * Real.log j < (poolMaximum n : ℝ) := by
    exact poolMaximum_lower lower n
  have hresult := Real.log_lt_log (mul_pos hsq hlogpos) (lt_trans hproduct hlower)
  rw [Real.log_mul (ne_of_gt hsq) (ne_of_gt hlogpos), Real.log_pow] at hresult
  simpa [a] using hresult

/-- The source's v-notation is admissible whenever v*ln(2)=ln(n); no
    natural logarithm is identified with a binary logarithm. -/
theorem poolMaximum_log_lower_v (lower : RSIndexLower) (n : ℕ) (hn : 2 ≤ n)
    (v : ℝ) (hv : v * Real.log 2 = Real.log (n : ℝ)) :
    2 * v * Real.log 2 + Real.log (2 * v * Real.log 2) <
      Real.log (poolMaximum n : ℝ) := by
  have hscale : 2 * v * Real.log 2 = 2 * Real.log (n : ℝ) := by
    rw [mul_assoc, hv]
  rw [hscale]
  exact poolMaximum_log_lower lower n hn

/-- The (3.13) upper estimate with its actual integer source domain. -/
theorem poolMaximum_upper (upper : RSIndexUpper) (n : ℕ)
    (hindex : 6 ≤ n * n + 1) :
    (poolMaximum n : ℝ) < ((n * n + 1 : ℕ) : ℝ) *
      (Real.log ((n * n + 1 : ℕ) : ℝ) +
        Real.log (Real.log ((n * n + 1 : ℕ) : ℝ))) := by
  simpa [poolMaximum] using upper (n * n + 1) hindex

/-- The sharper (3.11) upper estimate with its actual source domain. -/
theorem poolMaximum_upper_sharp (upper : RSIndexUpperSharp) (n : ℕ)
    (hindex : 20 ≤ n * n + 1) :
    (poolMaximum n : ℝ) < ((n * n + 1 : ℕ) : ℝ) *
      (Real.log ((n * n + 1 : ℕ) : ℝ) +
        Real.log (Real.log ((n * n + 1 : ℕ) : ℝ)) - 1 / 2) := by
  simpa [poolMaximum] using upper (n * n + 1) hindex

/-- Every order in the requested tail meets both upper-index source domains. -/
theorem tail_prime_index_domains {n : ℕ} (hn : 2001 ≤ n) :
    6 ≤ n * n + 1 ∧ 20 ≤ n * n + 1 := by
  have hmul : 5 * 5 ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- The S18.10 pool bound, uniformly through order 2^18. The only
    numerical logarithm enclosure is the kernel-checked mathlib theorem
    `Real.log_two_lt_d9`; all other comparisons are exact arithmetic. -/
theorem poolMaximum_below_two_pow_41 (upper : RSIndexUpper) (n : ℕ)
    (hn : 3 ≤ n) (hmax : n ≤ 2 ^ 18) : poolMaximum n < 2 ^ 41 := by
  have hj6 : 6 ≤ n * n + 1 := by
    have hmul : 3 * 3 ≤ n * n := Nat.mul_le_mul hn hn
    omega
  have hmul : n * n ≤ (2 ^ 18) * (2 ^ 18) := Nat.mul_le_mul hmax hmax
  have hjnat : n * n + 1 ≤ 2 ^ 36 + 1 := by
    norm_num at hmul ⊢
    omega
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hjpos : 0 < j := by
    dsimp [j]
    positivity
  have hjgt : 1 < j := by
    dsimp [j]
    exact_mod_cast (show 1 < n * n + 1 by omega)
  have hjlt : j < (2 : ℝ) ^ 37 := by
    have hjreal : j ≤ (2 : ℝ) ^ 36 + 1 := by
      dsimp [j]
      exact_mod_cast hjnat
    norm_num at hjreal ⊢
    linarith
  have hlog2 := Real.log_two_lt_d9
  have hlogj : Real.log j < 26 := by
    have h := Real.log_lt_log hjpos hjlt
    rw [Real.log_pow] at h
    norm_num at h
    linarith
  have hlogjpos : 0 < Real.log j := Real.log_pos hjgt
  have hlog26 : Real.log 26 < 4 := by
    have h := Real.log_lt_log (show (0 : ℝ) < 26 by norm_num)
      (show (26 : ℝ) < 2 ^ 5 by norm_num)
    rw [Real.log_pow] at h
    norm_num at h
    linarith
  have hloglogj : Real.log (Real.log j) < 4 :=
    lt_trans (Real.log_lt_log hlogjpos hlogj) hlog26
  have hu : (poolMaximum n : ℝ) < j * (Real.log j + Real.log (Real.log j)) := by
    exact poolMaximum_upper upper n hj6
  have hjreal : j ≤ (2 : ℝ) ^ 36 + 1 := by
    dsimp [j]
    exact_mod_cast hjnat
  have hfinal : (poolMaximum n : ℝ) < (2 : ℝ) ^ 41 := by
    have hsum : Real.log j + Real.log (Real.log j) < 30 := by linarith
    have hprod := mul_lt_mul_of_pos_left hsum hjpos
    calc
      (poolMaximum n : ℝ) < j * 30 := lt_trans hu hprod
      _ ≤ ((2 : ℝ) ^ 36 + 1) * 30 :=
        mul_le_mul_of_nonneg_right hjreal (by norm_num)
      _ < (2 : ℝ) ^ 41 := by norm_num
  exact_mod_cast hfinal

/-- The pool-index part of LZ9, uniformly through order 2^19. -/
theorem poolMaximum_below_two_pow_44 (upper : RSIndexUpper) (n : ℕ)
    (hn : 3 ≤ n) (hmax : n ≤ 2 ^ 19) : poolMaximum n < 2 ^ 44 := by
  have hj6 : 6 ≤ n * n + 1 := by
    have hmul : 3 * 3 ≤ n * n := Nat.mul_le_mul hn hn
    omega
  have hmul : n * n ≤ (2 ^ 19) * (2 ^ 19) := Nat.mul_le_mul hmax hmax
  have hjnat : n * n + 1 ≤ 2 ^ 38 + 1 := by
    norm_num at hmul ⊢
    omega
  let j : ℝ := ((n * n + 1 : ℕ) : ℝ)
  have hjpos : 0 < j := by
    dsimp [j]
    positivity
  have hjgt : 1 < j := by
    dsimp [j]
    exact_mod_cast (show 1 < n * n + 1 by omega)
  have hjreal : j ≤ (2 : ℝ) ^ 38 + 1 := by
    dsimp [j]
    exact_mod_cast hjnat
  have hjlt : j < (2 : ℝ) ^ 39 := by
    norm_num at hjreal ⊢
    linarith
  have hlog2 := Real.log_two_lt_d9
  have hlogj : Real.log j < 28 := by
    have h := Real.log_lt_log hjpos hjlt
    rw [Real.log_pow] at h
    norm_num at h
    linarith
  have hlogjpos : 0 < Real.log j := Real.log_pos hjgt
  have hlog28 : Real.log 28 < 4 := by
    have h := Real.log_lt_log (show (0 : ℝ) < 28 by norm_num)
      (show (28 : ℝ) < 2 ^ 5 by norm_num)
    rw [Real.log_pow] at h
    norm_num at h
    linarith
  have hloglogj : Real.log (Real.log j) < 4 :=
    lt_trans (Real.log_lt_log hlogjpos hlogj) hlog28
  have hu : (poolMaximum n : ℝ) < j * (Real.log j + Real.log (Real.log j)) :=
    poolMaximum_upper upper n hj6
  have hfinal : (poolMaximum n : ℝ) < (2 : ℝ) ^ 44 := by
    have hsum : Real.log j + Real.log (Real.log j) < 32 := by linarith
    have hprod := mul_lt_mul_of_pos_left hsum hjpos
    calc
      (poolMaximum n : ℝ) < j * 32 := lt_trans hu hprod
      _ ≤ ((2 : ℝ) ^ 38 + 1) * 32 :=
        mul_le_mul_of_nonneg_right hjreal (by norm_num)
      _ < (2 : ℝ) ^ 44 := by norm_num
  exact_mod_cast hfinal

/-- The finite BMOR argument cap follows for every entry in the pool.
    This is an index estimate only; it does not assert any BMOR theorem. -/
theorem pool_entry_below_ten_pow_13 (upper : RSIndexUpper) (n : ℕ)
    (hn : 3 ≤ n) (hmax : n ≤ 2 ^ 18) {p : ℕ} (hp : p ∈ pool n) :
    p < 10 ^ 13 := by
  have hX := poolMaximum_below_two_pow_41 upper n hn hmax
  have hcap : 2 ^ 41 < (10 : ℕ) ^ 13 := by decide
  exact lt_of_le_of_lt (pool_le_poolMaximum hp) (lt_trans hX hcap)

end
end Sude
