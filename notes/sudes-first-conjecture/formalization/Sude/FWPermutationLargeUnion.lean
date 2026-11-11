import Sude.FWPermutationLargeCut

/-! Union bound for FW's large cuts in the uniform permutation-triple space.
The bound includes complementary cuts and makes no derangement or existence claim. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- The FW failure event over qualifying sides of size at most `n/2` and at
least `n/256`. When `n` is even, both balanced complements may occur. -/
def fwPermutationLargeCutBad (n : ℕ) : Finset (Fin 3 → Equiv.Perm (Fin n)) :=
  (permutationLargeCuts n).biUnion fwPermutationFixedCutBad

/-- All qualifying cuts, including those with the larger side named, are
covered by the smaller-side event. -/
theorem fw_large_cut_mem_of_failure {n : ℕ} {p : Fin 3 → Equiv.Perm (Fin n)}
    (S : Finset (Fin n)) (hlarge : n ≤ 256 * min S.card (n - S.card))
    (hfail : fwPermutationCutFailure p S) : p ∈ fwPermutationLargeCutBad n := by
  classical
  have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
  by_cases hhalf : 2 * S.card ≤ n
  · apply Finset.mem_biUnion.mpr
    refine ⟨S, ?_, ?_⟩
    · simp only [permutationLargeCuts, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact hhalf
      · have hm := Nat.min_le_left S.card (n - S.card)
        omega
    · simpa [fwPermutationFixedCutBad] using hfail
  · apply Finset.mem_biUnion.mpr
    refine ⟨Sᶜ, ?_, ?_⟩
    · simp only [permutationLargeCuts, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.card_compl, Fintype.card_fin]
      have hm := Nat.min_le_right S.card (n - S.card)
      constructor <;> omega
    · simpa [fwPermutationFixedCutBad] using
        (fwPermutationCutFailure_compl p S).mpr hfail

/-- Group FW fixed-cut failure counts by size, using the exact binomial
multiplicity. -/
theorem fw_sum_cuts_by_size (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (∑ S ∈ permutationCutsOfSize n P, (fwPermutationFixedCutBad S).card) =
      ∑ s ∈ (Finset.range (n + 1)).filter P,
        Nat.choose n s * fwPermutationFixedCutCount n s := by
  classical
  let cuts := permutationCutsOfSize n P
  let sizes := (Finset.range (n + 1)).filter P
  have hmap : ∀ S ∈ cuts, S.card ∈ sizes := by
    intro S hS
    have hle : S.card ≤ n := by simpa using Finset.card_le_univ S
    have hP : P S.card := (Finset.mem_filter.mp hS).2
    simp [sizes, hP, hle]
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun S => (fwPermutationFixedCutBad S).card)]
  apply Finset.sum_congr rfl
  intro s hs
  have hsP : P s := (Finset.mem_filter.mp hs).2
  have hfiber : cuts.filter (fun S => S.card = s) =
      (Finset.univ : Finset (Fin n)).powersetCard s := by
    ext S
    simp only [cuts, permutationCutsOfSize, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_powersetCard, Finset.subset_univ]
    constructor
    · exact And.right
    · intro h
      exact ⟨h ▸ hsP, h⟩
  rw [Finset.sum_const_nat (m := fwPermutationFixedCutCount n s) (by
    intro S hS
    have hcard := (Finset.mem_filter.mp hS).2
    simpa [hcard] using fwPermutationFixedCutCount_spec S)]
  rw [hfiber, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The exact large-cut union bound grouped by smaller-side cardinality. -/
theorem fw_large_cut_union_card (n : ℕ) :
    (fwPermutationLargeCutBad n).card ≤
      ∑ s ∈ permutationLargeSizes n, Nat.choose n s * fwPermutationFixedCutCount n s := by
  classical
  have h := Finset.card_biUnion_le (s := permutationLargeCuts n) (t := fwPermutationFixedCutBad)
  change (fwPermutationLargeCutBad n).card ≤ _ at h
  have hcuts : permutationLargeCuts n =
      permutationCutsOfSize n (fun s => 2 * s ≤ n ∧ n ≤ 256 * s) := rfl
  rw [hcuts, fw_sum_cuts_by_size] at h
  exact h

/-- Summing the fixed-size FW estimates costs at most one factor `n+1`. -/
theorem fw_large_cut_sum_bound {n : ℕ} (hn : 0 < n) :
    ((∑ s ∈ permutationLargeSizes n, Nat.choose n s * fwPermutationFixedCutCount n s : ℕ) : ℝ) /
      (n.factorial : ℝ)^3 ≤ ((n + 1 : ℕ) : ℝ)^6 * Real.exp (-(n : ℝ) / 250) := by
  classical
  let A := permutationLargeSizes n
  let C : ℝ := ((n + 1 : ℕ) : ℝ)^5 * Real.exp (-(n : ℝ) / 250)
  have hsum : (∑ s ∈ A, ((Nat.choose n s : ℝ) * (fwPermutationFixedCutCount n s : ℝ)) /
      (n.factorial : ℝ)^3) ≤ (A.card : ℝ) * C := by
    have h := Finset.sum_le_card_nsmul A
      (fun s => ((Nat.choose n s : ℝ) * (fwPermutationFixedCutCount n s : ℝ)) /
        (n.factorial : ℝ)^3) C (by
        intro s hs
        have hs' := (Finset.mem_filter.mp hs).2
        have hspos : 0 < s := by omega
        exact fw_large_cut_summand_bound hspos hs'.1 hs'.2)
    simpa using h
  have hcard : A.card ≤ n + 1 := by
    have hsub : A ⊆ Finset.range (n + 1) := Finset.filter_subset _ _
    simpa using Finset.card_le_card hsub
  have hcardR : (A.card : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_right hcardR hC)
  have hsumid : ((∑ s ∈ A, Nat.choose n s * fwPermutationFixedCutCount n s : ℕ) : ℝ) /
      (n.factorial : ℝ)^3 = ∑ s ∈ A,
        ((Nat.choose n s : ℝ) * (fwPermutationFixedCutCount n s : ℝ)) / (n.factorial : ℝ)^3 := by
    push_cast
    rw [Finset.sum_div]
  rw [hsumid]
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ) * C := hsum'
    _ = _ := by dsimp [C]; ring

/-- The normalized probability of any FW large-cut failure under a uniform
triple of permutations, with the complementary side included. -/
theorem fw_large_cut_union_bound {n : ℕ} (hn : 0 < n) :
    ((fwPermutationLargeCutBad n).card : ℝ) / (n.factorial : ℝ)^3 ≤
      ((n + 1 : ℕ) : ℝ)^6 * Real.exp (-(n : ℝ) / 250) := by
  have hcard : ((fwPermutationLargeCutBad n).card : ℝ) ≤
      ((∑ s ∈ permutationLargeSizes n,
        Nat.choose n s * fwPermutationFixedCutCount n s : ℕ) : ℝ) := by
    exact_mod_cast fw_large_cut_union_card n
  exact (div_le_div_of_nonneg_right hcard (by positivity)).trans (fw_large_cut_sum_bound hn)

end
end Sude
