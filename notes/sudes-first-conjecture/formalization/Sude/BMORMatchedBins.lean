import Sude.APInterval

/-! Convert the exact finite BMOR interval theorem to disjoint FW bin stocks. -/
namespace Sude
noncomputable section

/-- Pairwise separated half-open intervals give disjoint actual prime stocks.
The modulus, residue, primality and endpoints are those of `apInterval`. -/
theorem apInterval_pairwise_disjoint {ι : Type*} (b c : ι → ℝ) (q : ℕ) (a : ℤ)
    (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i)
    (hsep : ∀ i j, i ≠ j → c i ≤ b j ∨ c j ≤ b i) :
    (Set.univ : Set ι).PairwiseDisjoint (fun i => apInterval (b i) (c i) q a) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hi := (mem_apInterval_iff (b i) (c i) q a (hb i) (hc i) p).mp hp
  have hj := (mem_apInterval_iff (b j) (c j) q a (hb j) (hc j) p).mp hq
  rcases hsep i j hij with h | h <;> linarith [hi.2.1, hi.2.2.1, hj.2.1, hj.2.2.1]

/-- The published finite BMOR input gives distinct prescribed-pool primes
in every separated modulus-two bin. The natural number `W` must be bounded
by the actual explicit endpoint estimate for each bin; no numerical gate or
source-specific interval containment is assumed. -/
theorem bmor_two_separated_bin_supplies {ι : Type*}
    (h : BMORFiniteTheta) (upper : RSIndexUpper) (n W : ℕ) (b c : ι → ℝ)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hb : ∀ i, 1 ≤ b i) (hbc : ∀ i, b i ≤ c i)
    (hcX : ∀ i, c i ≤ (poolMaximum n : ℝ))
    (hsep : ∀ i j, i ≠ j → c i ≤ b j ∨ c j ≤ b i)
    (hW : ∀ i, (W : ℝ) ≤
      ((c i - b i) - (518 / 125 : ℝ) * (Real.sqrt (b i) + Real.sqrt (c i))) /
        Real.log (poolMaximum n : ℝ)) :
    (Set.univ : Set ι).PairwiseDisjoint (fun i => apInterval (b i) (c i) 2 1) ∧
      (∀ i, W ≤ (apInterval (b i) (c i) 2 1).card) ∧
      (∀ i p, p ∈ apInterval (b i) (c i) 2 1 → p ∈ pool n) := by
  have hb0 : ∀ i, 0 ≤ b i := fun i => le_trans (by norm_num) (hb i)
  have hc0 : ∀ i, 0 ≤ c i := fun i => (hb0 i).trans (hbc i)
  refine ⟨apInterval_pairwise_disjoint b c 2 1 hb0 hc0 hsep, ?_, ?_⟩
  · intro i
    have hs := bmor_two_pool_interval_supply h upper n (b i) (c i) hn hnmax (hb i) (hbc i) (hcX i)
    have hreal : (W : ℝ) ≤ (apInterval (b i) (c i) 2 1).card := (hW i).trans hs.1
    exact_mod_cast hreal
  · intro i p hp
    exact (bmor_two_pool_interval_supply h upper n (b i) (c i) hn hnmax (hb i) (hbc i) (hcX i)).2 p hp

end
end Sude
