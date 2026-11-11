import Sude.Placement

/-! The exact subset-sum grids used by the finite prefix and bridge stages.
These lemmas do not assert the existence of any prime pairs. -/
namespace Sude
noncomputable section

/-- Every number below 2^P has a representation using distinct stages. -/
theorem binary_subset_sum (P m : ℕ) (hm : m < 2 ^ P) :
    ∃ S : Finset ℕ, S ⊆ Finset.range P ∧ (∑ j ∈ S, 2 ^ j) = m := by
  induction P generalizing m with
  | zero =>
    have : m = 0 := by simp at hm; omega
    subst m
    exact ⟨∅, by simp, by simp⟩
  | succ P ih =>
    by_cases hsmall : m < 2 ^ P
    · obtain ⟨S, hS, hsum⟩ := ih m hsmall
      refine ⟨S, ?_, hsum⟩
      exact hS.trans (Finset.range_subset_range.mpr (by omega))
    · have hlarge : 2 ^ P ≤ m := by omega
      have hrest : m - 2 ^ P < 2 ^ P := by
        rw [pow_succ] at hm
        omega
      obtain ⟨S, hS, hsum⟩ := ih (m - 2 ^ P) hrest
      have hnot : P ∉ S := by
        intro hmem
        have := hS hmem
        simp only [Finset.mem_range] at this
        omega
      refine ⟨insert P S, ?_, ?_⟩
      · intro j hj
        simp only [Finset.mem_insert, Finset.mem_range] at hj ⊢
        rcases hj with rfl | hj
        · omega
        · have hj' := hS hj
          simp only [Finset.mem_range] at hj'
          omega
      · rw [Finset.sum_insert hnot, hsum]
        omega

/-- FPF1: gaps 2,4,...,2^P produce every even correction through
    2^(P+1)-2, with each physical stage used at most once. -/
theorem binary_even_grid (P t : ℕ) (heven : 2 ∣ t)
    (hbound : t ≤ 2 ^ (P + 1) - 2) :
    ∃ S : Finset ℕ, S ⊆ Finset.range P ∧ (∑ j ∈ S, 2 ^ (j + 1)) = t := by
  obtain ⟨m, hm⟩ := heven
  subst t
  have hpos : 0 < 2 ^ P := Nat.two_pow_pos P
  have hm : m < 2 ^ P := by
    rw [pow_succ] at hbound
    omega
  obtain ⟨S, hS, hsum⟩ := binary_subset_sum P m hm
  refine ⟨S, hS, ?_⟩
  simp only [pow_succ, ← Finset.sum_mul, hsum]
  omega

/-- Every even demand through R is a subset sum of the labelled gaps. -/
def CompleteEvenGrid {α : Type*} (S : Finset α) (gap : α → ℕ) (R : ℕ) : Prop :=
  ∀ t, t ≤ R → 2 ∣ t → ∃ T : Finset α, T ⊆ S ∧ (∑ i ∈ T, gap i) = t

/-- Appending an even gap at most R+2 preserves the complete even grid.
The new physical label must not already occur in the previous reservoir. -/
theorem completeEvenGrid_insert {α : Type*} [DecidableEq α]
    (S : Finset α) (gap : α → ℕ) (R : ℕ) (k : α)
    (hk : k ∉ S) (hR : 2 ∣ R) (hgap : 2 ∣ gap k) (hjoin : gap k ≤ R + 2)
    (hcomplete : CompleteEvenGrid S gap R) :
    CompleteEvenGrid (insert k S) gap (R + gap k) := by
  intro t ht heven
  by_cases hsmall : t ≤ R
  · obtain ⟨T, hT, hsum⟩ := hcomplete t hsmall heven
    exact ⟨T, hT.trans (Finset.subset_insert k S), hsum⟩
  · have hge : gap k ≤ t := by
      obtain ⟨r, hr⟩ := hR
      obtain ⟨z, hz⟩ := heven
      omega
    have hrest : t - gap k ≤ R := by omega
    have hevenRest : 2 ∣ t - gap k := Nat.dvd_sub heven hgap
    obtain ⟨T, hT, hsum⟩ := hcomplete (t - gap k) hrest hevenRest
    have hnot : k ∉ T := fun hmem => hk (hT hmem)
    refine ⟨insert k T, ?_, ?_⟩
    · exact Finset.insert_subset_insert k hT
    · rw [Finset.sum_insert hnot, hsum]
      omega

end
end Sude
