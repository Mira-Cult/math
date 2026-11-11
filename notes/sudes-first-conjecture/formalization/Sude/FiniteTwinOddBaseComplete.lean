import Sude.FiniteTwinOddBaseOrder
import Sude.FiniteTwinOddBaseLucas

/-! Derive a complete explicit base from checked primes and a checked count. -/
namespace Sude
noncomputable section

/-- The generated odd list contains only primes in the required domain. -/
theorem finiteTwinOddBase_valid : ∀ p ∈ finiteTwinOddBase,
    Nat.Prime p ∧ 3 ≤ p ∧ p ≤ 32768 := by
  simpa only [List.all_eq_true, decide_eq_true_eq] using finiteTwinOddBase_all

/-- Exact cardinality follows from the checked strict ordering. -/
theorem finiteTwinOddBase_card : finiteTwinOddBase.toFinset.card = 3511 := by
  rw [List.toFinset_card_of_nodup finiteTwinOddBase_sorted.pairwise.nodup,
    finiteTwinOddBase_length]

/-- An independently checked prime-prefix count proves the listed primes
exhaust the entire odd prime segment, not just a subset. -/
theorem finiteTwinOddBase_exhaustive :
    finiteTwinOddBase.toFinset = oddPrimeSegment 3 32771 := by
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    have h := finiteTwinOddBase_valid p (List.mem_toFinset.mp hp)
    simp only [oddPrimeSegment, Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨h.2.1, by omega⟩, h.1, by omega⟩
  · rw [streamingFirst16384_prime_count_sum.1, finiteTwinOddBase_card]

/-- The finite source's complete base, written as a literal list whose
correctness is proved from primality checks and the verified prefix count. -/
def finiteTwinCheckedBase : List ℕ := 2 :: finiteTwinOddBase

theorem finiteTwinCheckedBase_complete : CompletePrimeBase finiteTwinCheckedBase.toFinset 32768 := by
  intro p
  simp only [finiteTwinCheckedBase, List.toFinset_cons, Finset.mem_insert]
  constructor
  · rintro (rfl | hp)
    · exact ⟨by decide, by decide⟩
    · have h := finiteTwinOddBase_valid p (List.mem_toFinset.mp hp)
      exact ⟨h.1, h.2.2⟩
  · rintro ⟨hp, hbound⟩
    by_cases h2 : p = 2
    · exact Or.inl h2
    · right
      rw [finiteTwinOddBase_exhaustive]
      simp only [oddPrimeSegment, Finset.mem_filter, Finset.mem_Ico]
      have hp2 := hp.two_le
      exact ⟨⟨by omega, by omega⟩, hp, h2⟩

end
end Sude
