import Sude.PermutationJointLaw

/-! Group the exact fixed-cut law by cut size and combine failure events. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- The exact hypergeometric numerator for a cut of size `s`. -/
def permutationCutWeight (n s : ℕ) : ℕ :=
  ∑ j ∈ (Finset.univ : Finset (Fin 3 → Fin (s + 1))).filter
      (fun j => 400 * (∑ i, (j i).val) < 199 * min s (n - s)),
    ∏ i, (Nat.choose s (j i).val * Nat.choose (n - s) (j i).val)

/-- The exact fixed-cut law depends only on the cardinality of the cut. -/
theorem permutationFixedCutBad_scaled_card {n : ℕ} (S : Finset (Fin n)) :
    (Nat.choose n S.card)^3 * (permutationFixedCutBad S).card =
      (n.factorial)^3 * permutationCutWeight n S.card := by
  exact permutationFixedCutBad_hypergeometric S

/-- All cuts of a given size have equally many failing permutation triples. -/
theorem permutationFixedCutBad_card_eq {n : ℕ} (S T : Finset (Fin n))
    (hcard : S.card = T.card) :
    (permutationFixedCutBad S).card = (permutationFixedCutBad T).card := by
  have hs := permutationFixedCutBad_scaled_card S
  have ht := permutationFixedCutBad_scaled_card T
  rw [hcard] at hs
  have hchoose : 0 < Nat.choose n T.card := Nat.choose_pos (by simpa using Finset.card_le_univ T)
  have hpow : 0 < (Nat.choose n T.card)^3 := pow_pos hchoose _
  exact Nat.eq_of_mul_eq_mul_left hpow (hs.trans ht.symm)

/-- Candidate smaller-side cuts in the source small-cut range. -/
def permutationSmallCuts (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter
    (fun S => 2 * S.card ≤ n ∧ 256 * S.card < n)

/-- Candidate smaller-side cuts in the source large-cut range. -/
def permutationLargeCuts (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter
    (fun S => 2 * S.card ≤ n ∧ n ≤ 256 * S.card)

/-- The actual small-cut failure event is the finite union over small cuts. -/
theorem permutationSmallCutBad_eq_biUnion (n : ℕ) :
    permutationSmallCutBad n = (permutationSmallCuts n).biUnion permutationFixedCutBad := by
  classical
  ext p
  rw [mem_permutationSmallCutBad_iff]
  simp only [Finset.mem_biUnion, permutationSmallCuts, permutationFixedCutBad,
    Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- The actual large-cut failure event is the finite union over large cuts. -/
theorem permutationLargeCutBad_eq_biUnion (n : ℕ) :
    permutationLargeCutBad n = (permutationLargeCuts n).biUnion permutationFixedCutBad := by
  classical
  ext p
  rw [mem_permutationLargeCutBad_iff]
  simp only [Finset.mem_biUnion, permutationLargeCuts, permutationFixedCutBad,
    Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- Union bound with no disjointness or event-independence hypothesis. -/
theorem permutation_cut_union_bounds (n : ℕ) :
    (permutationSmallCutBad n).card ≤
        ∑ S ∈ permutationSmallCuts n, (permutationFixedCutBad S).card ∧
      (permutationLargeCutBad n).card ≤
        ∑ S ∈ permutationLargeCuts n, (permutationFixedCutBad S).card := by
  constructor
  · rw [permutationSmallCutBad_eq_biUnion]
    exact Finset.card_biUnion_le
  · rw [permutationLargeCutBad_eq_biUnion]
    exact Finset.card_biUnion_le

/-- A canonical subset of a given size, used only as a representative. -/
def permutationCanonicalCut (n s : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x => x.val < s)

theorem permutationCanonicalCut_card {n s : ℕ} (hs : s ≤ n) :
    (permutationCanonicalCut n s).card = s := by
  rw [permutationCanonicalCut, Fin.card_filter_val_lt, Nat.min_eq_right hs]

/-- Exact fixed-cut count, indexed by cut size. -/
def permutationFixedCutCount (n s : ℕ) : ℕ :=
  (permutationFixedCutBad (permutationCanonicalCut n s)).card

theorem permutationFixedCutCount_spec {n : ℕ} (S : Finset (Fin n)) :
    (permutationFixedCutBad S).card = permutationFixedCutCount n S.card := by
  unfold permutationFixedCutCount
  apply permutationFixedCutBad_card_eq
  exact (permutationCanonicalCut_card (by simpa using Finset.card_le_univ S)).symm

/-- All cuts whose cardinality satisfies a decidable size condition. -/
def permutationCutsOfSize (n : ℕ) (P : ℕ → Prop) [DecidablePred P] : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun S => P S.card)

/-- Every union-bound sum over cuts can be grouped by size. The coefficient
is the exact number of subsets, `choose n s`, and no cut is sampled. -/
theorem permutation_sum_cuts_by_size (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (∑ S ∈ permutationCutsOfSize n P, (permutationFixedCutBad S).card) =
      ∑ s ∈ (Finset.range (n + 1)).filter P,
        Nat.choose n s * permutationFixedCutCount n s := by
  classical
  let cuts := permutationCutsOfSize n P
  let sizes := (Finset.range (n + 1)).filter P
  have hmap : ∀ S ∈ cuts, S.card ∈ sizes := by
    intro S hS
    have hle : S.card ≤ n := by simpa using Finset.card_le_univ S
    have hP : P S.card := (Finset.mem_filter.mp hS).2
    simp [sizes, hP, hle]
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun S => (permutationFixedCutBad S).card)]
  apply Finset.sum_congr rfl
  intro s hs
  have hsP : P s := (Finset.mem_filter.mp hs).2
  have hsle : s ≤ n := by
    have := (Finset.mem_filter.mp hs).1
    simp only [Finset.mem_range] at this
    omega
  have hfiber : cuts.filter (fun S => S.card = s) =
      (Finset.univ : Finset (Fin n)).powersetCard s := by
    ext S
    simp only [cuts, permutationCutsOfSize, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_powersetCard, Finset.subset_univ]
    constructor
    · exact And.right
    · intro h
      exact ⟨h ▸ hsP, h⟩
  rw [Finset.sum_const_nat (m := permutationFixedCutCount n s) (by
    intro S hS
    have hcard := (Finset.mem_filter.mp hS).2
    simpa [hcard] using permutationFixedCutCount_spec S)]
  rw [hfiber, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The exact cut-size representative has the same scaled hypergeometric
law as every actual cut of that size. -/
theorem permutationFixedCutCount_scaled {n s : ℕ} (hs : s ≤ n) :
    (Nat.choose n s)^3 * permutationFixedCutCount n s =
      (n.factorial)^3 * permutationCutWeight n s := by
  have h := permutationFixedCutBad_scaled_card (permutationCanonicalCut n s)
  rw [permutationCanonicalCut_card hs] at h
  exact h

/-- Cut sizes in the small and large source regimes. -/
def permutationSmallSizes (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun s => 2 * s ≤ n ∧ 256 * s < n)

def permutationLargeSizes (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun s => 2 * s ≤ n ∧ n ≤ 256 * s)

/-- Source small and large failure events satisfy exact-size union bounds. -/
theorem permutation_cut_union_bounds_by_size (n : ℕ) :
    (permutationSmallCutBad n).card ≤
      ∑ s ∈ permutationSmallSizes n, Nat.choose n s * permutationFixedCutCount n s ∧
    (permutationLargeCutBad n).card ≤
      ∑ s ∈ permutationLargeSizes n, Nat.choose n s * permutationFixedCutCount n s := by
  classical
  obtain ⟨hs, hl⟩ := permutation_cut_union_bounds n
  have hsmall : permutationSmallCuts n =
      permutationCutsOfSize n (fun s => 2 * s ≤ n ∧ 256 * s < n) := by rfl
  have hlarge : permutationLargeCuts n =
      permutationCutsOfSize n (fun s => 2 * s ≤ n ∧ n ≤ 256 * s) := by rfl
  rw [hsmall, permutation_sum_cuts_by_size] at hs
  rw [hlarge, permutation_sum_cuts_by_size] at hl
  exact ⟨hs, hl⟩

/-- A numerical bound on the two explicit sums yields actual degree-six
permutation graphs with the FC2K expansion needed by the routing interface. -/
theorem exists_permutation_expander_of_cut_sums {n : ℕ} (hn : 2 ≤ n)
    (hbudget : 27 *
      ((∑ s ∈ permutationSmallSizes n, Nat.choose n s * permutationFixedCutCount n s) +
       (∑ s ∈ permutationLargeSizes n, Nat.choose n s * permutationFixedCutCount n s)) <
        (n.factorial)^3) :
    ∃ p : Fin 3 → Equiv.Perm (Fin n),
      (∀ i v, p i v ≠ v) ∧
      ∀ S : Finset (Fin n),
        199 * min S.card (n - S.card) ≤
          200 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card := by
  have hb := permutation_cut_union_bounds_by_size n
  have htotal : Fintype.card (Fin 3 → Equiv.Perm (Fin n)) = (n.factorial)^3 := by
    simp [Fintype.card_perm]
  apply exists_permutation_expander_of_bad_card hn
  rw [htotal]
  omega

end
end Sude
