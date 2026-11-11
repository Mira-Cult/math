import Sude.FWSeedBridge
import Sude.FWPoolBound
import Sude.ScreenedPool

/-! FW2 candidate selection specialized to the actual prescribed pool. -/
namespace Sude

/-- Once the source's finite twin-prime population is established, the FW
candidate quota survives the prior bridge reservation in the prescribed pool.
The only analytic premise is the published prime-index lower bound. -/
theorem fw_actual_seed_candidates_after_bridges (lower : RSIndexLower)
    (n : ℕ) (seeds bridges : Finset ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hbridge : ∀ p ∈ bridges, poolMaximum n ≤ 4 * p)
    (hcount : 3650551 ≤ seeds.card) :
    ∃ candidates : Finset ℕ,
      candidates ⊆ seeds ∧ candidates.card = 6 * (n + 8) * (16 + 2 - 1) ∧
      PairwiseDisjointPairs candidates 2 ∧
      pairFootprint candidates 2 ⊆ poolFinset n \ bridges ∧
      (pairFootprint candidates 2).card = 2 * (6 * (n + 8) * (16 + 2 - 1)) := by
  have hmax := fw_poolMaximum_gt_four_seed lower hnlo
  have hpool : ∀ p ∈ seeds, p ∈ poolFinset n ∧ p + 2 ∈ poolFinset n := by
    intro p hp
    obtain ⟨hbig, hpprime, hqprime⟩ := hprime p hp
    have hbound := hseed p hp
    constructor <;> apply mem_poolFinset.mpr
    · exact prime_mem_pool_of_le_max hpprime (by omega) (by omega)
    · exact prime_mem_pool_of_le_max hqprime (by omega) (by omega)
  have hmatch : PairwiseDisjointPairs seeds 2 := by
    apply binary_prime_family_disjoint seeds 1
    intro p hp
    obtain ⟨hbig, hpprime, hqprime⟩ := hprime p hp
    simpa using (show 3 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2) from ⟨by omega, hpprime, hqprime⟩)
  exact fw_seed_candidates_after_bridges (poolFinset n) seeds bridges n (poolMaximum n)
    hnhi hmax hseed hbridge hpool hmatch hcount

end Sude
