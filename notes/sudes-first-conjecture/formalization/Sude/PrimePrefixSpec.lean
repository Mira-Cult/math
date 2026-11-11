import Sude.PrefixCount
import Sude.TargetRouting

/-! Exact correspondence between a verified odd-prime prefix and the
prescribed pool. Numerical prefix certificates remain separate obligations. -/
namespace Sude
noncomputable section

/-- The exact prescribed pool is exactly the odd-prime prefix through its
maximum, including the empty pool at order zero. -/
theorem pool_eq_prefix (n : ℕ) :
    pool n = (oddPrimePrefix (poolMaximum n) : Set ℕ) := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, rfl⟩ := hp
    have hprime : Nat.Prime (oddPrime i.val) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (i.val + 1)
    have hodd := oddPrime_odd i.val
    have hne : oddPrime i.val ≠ 2 := by intro h; rw [h] at hodd; norm_num at hodd
    have hle : oddPrime i.val ≤ poolMaximum n := pool_le_poolMaximum ⟨i, rfl⟩
    change oddPrime i.val ∈ oddPrimePrefix (poolMaximum n)
    simp only [oddPrimePrefix, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hprime, hne⟩
  · intro hp
    change p ∈ oddPrimePrefix (poolMaximum n) at hp
    simp only [oddPrimePrefix, Finset.mem_filter, Finset.mem_range] at hp
    exact prime_mem_pool_of_le_max hp.2.1 hp.2.2 (by omega)

/-- The exact pool sum is the sum of the odd primes through its maximum. -/
theorem poolTotal_eq_prefix_sum (n : ℕ) :
    Lucas.poolTotal n = ∑ p ∈ oddPrimePrefix (poolMaximum n), p := by
  classical
  let f : Fin (n * n) → ℕ := fun i => oddPrime i.val
  have hinj : Function.Injective f := by
    intro i j hij
    exact Fin.ext (oddPrime_injective hij)
  have hset : Finset.univ.image f = oddPrimePrefix (poolMaximum n) := by
    ext p
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    change (∃ i : Fin (n * n), f i = p) ↔ p ∈ (oddPrimePrefix (poolMaximum n) : Set ℕ)
    exact Set.ext_iff.mp (pool_eq_prefix n) p
  unfold Lucas.poolTotal
  rw [← hset, Finset.sum_image]
  exact hinj.injOn

/-- A prime endpoint and an exact odd-prefix count determine its prime index. -/
theorem poolMaximum_eq_of_oddPrefix_count {n X : ℕ} (hX : Nat.Prime X)
    (hcount : (oddPrimePrefix X).card = n * n) :
    poolMaximum n = X := by
  have hcount' := prime_count_succ_eq_oddPrefix_add_one hX.two_le
  rw [hcount] at hcount'
  have hcnt : Nat.count Nat.Prime X = n * n := by
    rw [Nat.count_succ, if_pos hX] at hcount'
    omega
  change Nat.nth Nat.Prime (n * n) = X
  rw [← hcnt, Nat.nth_count hX]

/-- The exact source interface for FTT2. A separately verified numerical
prefix count and sum determine the recorded X and T. -/
theorem pool_identities_of_oddPrefix_certificate {n X T : ℕ}
    (hX : Nat.Prime X)
    (hcount : (oddPrimePrefix X).card = n * n)
    (hsum : (∑ p ∈ oddPrimePrefix X, p) = T) :
    poolMaximum n = X ∧ Lucas.poolTotal n = T := by
  have hmax := poolMaximum_eq_of_oddPrefix_count hX hcount
  refine ⟨hmax, ?_⟩
  rw [poolTotal_eq_prefix_sum n, hmax, hsum]

end
end Sude
