import Sude.PrimeIndex

/-! Translation of the finite FPF odd-prime prefix count into exact pool
membership. The individual numerical prefix counts remain unproved. -/
namespace Sude

noncomputable section

def oddPrimePrefix (B : ℕ) : Finset ℕ :=
  (Finset.range (B + 1)).filter (fun p => Nat.Prime p ∧ p ≠ 2)

/-- Through B ≥ 2, the full prime prefix consists exactly of 2 and the odd
prime prefix; every number is counted once. -/
theorem prime_count_succ_eq_oddPrefix_add_one {B : ℕ} (hB : 2 ≤ B) :
    Nat.count Nat.Prime (B + 1) = (oddPrimePrefix B).card + 1 := by
  classical
  have hset : (Finset.range (B + 1)).filter Nat.Prime = insert 2 (oddPrimePrefix B) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, oddPrimePrefix]
    constructor
    · rintro ⟨hpB, hp⟩
      by_cases h : p = 2
      · exact Or.inl h
      · exact Or.inr ⟨hpB, hp, h⟩
    · rintro (rfl | ⟨hpB, hp, hne⟩)
      · exact ⟨by omega, Nat.prime_two⟩
      · exact ⟨hpB, hp⟩
  have hnot : 2 ∉ oddPrimePrefix B := by simp [oddPrimePrefix]
  rw [Nat.count_eq_card_filter_range, hset, Finset.card_insert_of_notMem hnot]

/-- The finite-prefix bound used in FPF1 really puts every odd prime at most B
in the first n² odd primes. It requires only an upper bound on the odd-prime
count, not the truth of any unverified table entry. -/
theorem prime_mem_pool_of_oddPrefix_card_le {n B p : ℕ} (hB : 2 ≤ B)
    (hcount : (oddPrimePrefix B).card ≤ n * n) (hp : Nat.Prime p)
    (hne : p ≠ 2) (hpB : p ≤ B) : p ∈ pool n := by
  have hcount' : Nat.count Nat.Prime (B + 1) ≤ n * n + 1 := by
    rw [prime_count_succ_eq_oddPrefix_add_one hB]
    omega
  have hindex : Nat.count Nat.Prime p ≤ n * n := by
    have hlt := Nat.count_strict_mono hp (show p < B + 1 by omega)
    omega
  have hmax : p ≤ poolMaximum n := by
    rw [poolMaximum, ← Nat.nth_count hp]
    exact Nat.nth_monotone Nat.infinite_setOfPred_prime hindex
  exact prime_mem_pool_of_le_max hp hne hmax

end
end Sude
