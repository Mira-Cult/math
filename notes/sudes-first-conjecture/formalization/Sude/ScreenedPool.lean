import Sude.PrefixCount
import Sude.NarrowPoolValues

/-! Exact prescribed-pool screening above 43. -/
namespace Sude
noncomputable section

/-- Finite representation of the exact `n²`-element prescribed pool. -/
def poolFinset (n : ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin (n * n))).image (fun i => oddPrime i.val)

theorem mem_poolFinset {n p : ℕ} : p ∈ poolFinset n ↔ p ∈ pool n := by
  simp [poolFinset, pool]

theorem poolFinset_card (n : ℕ) : (poolFinset n).card = n * n := by
  rw [poolFinset, Finset.card_image_of_injective]
  · simp
  · intro i j h
    exact Fin.ext (oddPrime_injective h)

theorem oddPrime_gt_two (i : ℕ) : 2 < oddPrime i := by
  have h := (Nat.nth_strictMono Nat.infinite_setOfPred_prime) (show 0 < i + 1 by omega)
  simpa [oddPrime] using h

theorem pool_prime_and_residue {n p : ℕ} (hp : p ∈ pool n) :
    Nat.Prime p ∧ p % 2 = 1 := by
  obtain ⟨i, rfl⟩ := hp
  have hprime : Nat.Prime (oddPrime i.val) :=
    Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (i.val + 1)
  exact ⟨hprime, hprime.eq_two_or_odd.resolve_left (ne_of_gt (oddPrime_gt_two i.val))⟩

/-- Exactly the thirteen odd primes through 43 are screened out once the
pool contains at least thirteen entries. -/
theorem screened_pool_card (n : ℕ) (hn : 13 ≤ n * n) :
    ((poolFinset n).filter fun p => 43 < p).card + 13 = n * n := by
  have hsmall : (oddPrimePrefix 43).card = 13 := by decide
  have hfilter : (poolFinset n).filter (fun p => p ≤ 43) = oddPrimePrefix 43 := by
    ext p
    simp only [Finset.mem_filter, mem_poolFinset, oddPrimePrefix, Finset.mem_range]
    constructor
    · rintro ⟨⟨i, rfl⟩, hp⟩
      have hprime : Nat.Prime (oddPrime i.val) :=
        Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (i.val + 1)
      exact ⟨Nat.lt_succ_of_le hp, hprime, ne_of_gt (oddPrime_gt_two i.val)⟩
    · rintro ⟨hp, hprime, hne⟩
      refine ⟨prime_mem_pool_of_oddPrefix_card_le (B := 43) (by decide) ?_ hprime hne (by omega), by omega⟩
      simpa [hsmall] using hn
  have hc := Finset.card_filter_add_card_filter_not (s := poolFinset n) (fun p => 43 < p)
  have heq : (poolFinset n).filter (fun p => ¬43 < p) = oddPrimePrefix 43 := by
    simpa only [not_lt] using hfilter
  rw [heq, hsmall, poolFinset_card] at hc
  exact hc

/-- Deleting any reserved values charges at most their actual cardinality;
the survivors remain genuine prescribed-pool entries above 43. -/
theorem screened_pool_after_reservations (n : ℕ) (reserved : Finset ℕ) (hn : 13 ≤ n * n) :
    let available := (poolFinset n).filter (fun p => 43 < p) \ reserved
    n * n ≤ available.card + reserved.card + 13 ∧
      ∀ p ∈ available, p ∈ pool n ∧ 43 < p := by
  dsimp only
  let screened := (poolFinset n).filter fun p => 43 < p
  have hc := Finset.card_sdiff_add_card screened reserved
  have hle : screened.card ≤ (screened ∪ reserved).card := Finset.card_le_card (Finset.subset_union_left)
  have hexact := screened_pool_card n hn
  refine ⟨?_, ?_⟩
  · dsimp [screened] at hc hle
    omega
  · intro p hp
    have hp' := Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1
    exact ⟨mem_poolFinset.mp hp'.1, hp'.2⟩

/-- The exact screened stock supplies the prime, interval, mod-2 and
midpoint-bin hypotheses of the `g=2` prefix phases after any reservations. -/
theorem screened_pool_phase_inputs (n z : ℕ) (reserved : Finset ℕ)
    (hn : 13 ≤ n * n) (hz : 0 < z) :
    let S := (poolFinset n).filter (fun p => 43 < p) \ reserved
    ((n * n : ℕ) : ℝ) - 13 - reserved.card ≤ S.card ∧
      (∀ p ∈ S, p ∈ pool n) ∧ (∀ p ∈ S, Nat.Prime p) ∧
      (∀ p ∈ S, (1 : ℝ) ≤ p ∧ (p : ℝ) ≤ 1 + poolMaximum n) ∧
      (∀ p ∈ S, p % 2 ∈ ({1} : Finset ℕ)) ∧
      0 < (poolMaximum n : ℝ) / z ∧
      (∀ p ∈ S, (1 : ℝ) ≤ p ∧ (p : ℝ) < 1 + z * ((poolMaximum n : ℝ) / z)) := by
  dsimp only
  let S := (poolFinset n).filter (fun p => 43 < p) \ reserved
  have hstock := screened_pool_after_reservations n reserved hn
  have hcard : ((n * n : ℕ) : ℝ) ≤ (S.card : ℝ) + reserved.card + 13 := by
    exact_mod_cast hstock.1
  have hpool : ∀ p ∈ S, p ∈ pool n := fun p hp => (hstock.2 p hp).1
  have hmid := prescribed_pool_midpoint_span S n z hz hpool
  refine ⟨by linarith, hpool, ?_, ?_, ?_, hmid.1, hmid.2⟩
  · intro p hp
    exact (pool_prime_and_residue (hpool p hp)).1
  · intro p hp
    have hpos : (1 : ℝ) ≤ p := hmid.2 p hp |>.1
    have hbound : (p : ℝ) ≤ poolMaximum n := by exact_mod_cast pool_le_poolMaximum (hpool p hp)
    exact ⟨hpos, by linarith⟩
  · intro p hp
    simpa using (pool_prime_and_residue (hpool p hp)).2

end
end Sude
