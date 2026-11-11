import Sude.DoublePairStock
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! FW8: finite matched-bin pair counting and repeated physical gaps. -/
namespace Sude
noncomputable section

/-- The total matched stock controls the number of matched cross-pairs.
This is a finite Cauchy inequality, without any stock or primality premise. -/
theorem matched_bin_stock_sq_le {N : ℕ} (low high : Fin N → Finset ℕ) :
    ((∑ i, min (low i).card (high i).card : ℕ) : ℝ) ^ 2 ≤
      (N : ℝ) * ∑ i, (((low i).card : ℝ) * (high i).card) := by
  let count : Fin N → ℝ := fun i => (min (low i).card (high i).card : ℝ)
  have hc : (∑ i, count i) ^ 2 ≤ (∑ i, (count i) ^ 2) * (N : ℝ) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ count (fun _ => (1 : ℝ))
    simpa using h
  have hp : (∑ i, (count i) ^ 2) ≤ ∑ i, (((low i).card : ℝ) * (high i).card) := by
    apply Finset.sum_le_sum
    intro i _
    have hl : count i ≤ (low i).card := by
      dsimp [count]
      exact_mod_cast Nat.min_le_left (low i).card (high i).card
    have hh : count i ≤ (high i).card := by
      dsimp [count]
      exact_mod_cast Nat.min_le_right (low i).card (high i).card
    have hn : 0 ≤ count i := by dsimp [count]; positivity
    nlinarith
  have hN : 0 ≤ (N : ℝ) := by positivity
  have hsum : ((∑ i, min (low i).card (high i).card : ℕ) : ℝ) = ∑ i, count i := by
    simp [count]
  rw [hsum]
  nlinarith [mul_le_mul_of_nonneg_right hp hN]

/-- If the total matched cross-pair population exceeds the number of gap
labels, two pairs have the same positive gap and four distinct endpoints.
The two pairs may belong to different matched bins. -/
theorem matched_bins_repeated_difference {N : ℕ} (low high : Fin N → Finset ℕ)
    (differences : Finset ℕ)
    (hlowdis : ∀ i j, i ≠ j → Disjoint (low i) (low j))
    (horder : ∀ i j a, a ∈ low i → ∀ b, b ∈ high j → a < b)
    (hdiff : ∀ i a, a ∈ low i → ∀ b, b ∈ high i → b - a ∈ differences)
    (hgate : (N : ℝ) * differences.card <
      ((∑ i, min (low i).card (high i).card : ℕ) : ℝ) ^ 2) :
    ∃ b : DoublePair, (∃ i, b.low₁ ∈ low i ∧ b.high₁ ∈ high i) ∧
      (∃ j, b.low₂ ∈ low j ∧ b.high₂ ∈ high j) ∧
      b.low₁ ≠ b.low₂ ∧ b.high₁ ≠ b.high₂ ∧ b.low₁ < b.high₁ ∧
      b.low₂ < b.high₂ ∧ b.low₁ < b.high₂ ∧ b.low₂ < b.high₁ ∧
      b.high₁ - b.low₁ = b.high₂ - b.low₂ := by
  classical
  let pairs : Finset (ℕ × ℕ) := Finset.univ.biUnion (fun i : Fin N => low i ×ˢ high i)
  have hdis : (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint
      (fun i => low i ×ˢ high i) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact Finset.disjoint_left.mp (hlowdis i j hij) (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hq).1
  have hcard : pairs.card = ∑ i, (low i).card * (high i).card := by
    simp [pairs, Finset.card_biUnion hdis]
  have hN : 0 < (N : ℝ) := by
    by_contra hnpos
    have hnzero : (N : ℝ) = 0 := le_antisymm (le_of_not_gt hnpos) (by positivity)
    have hzero : N = 0 := by exact_mod_cast hnzero
    subst N
    simp at hgate
  have hstock := matched_bin_stock_sq_le low high
  have hcountR : (differences.card : ℝ) < (pairs.card : ℝ) := by
    rw [hcard, Nat.cast_sum]
    push_cast
    nlinarith
  have hcount : differences.card < pairs.card := by exact_mod_cast hcountR
  obtain ⟨x, hx, y, hy, hxy, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcount
      (f := fun p : ℕ × ℕ => p.2 - p.1) (by
        intro p hp
        obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
        exact hdiff i p.1 (Finset.mem_product.mp hi).1 p.2 (Finset.mem_product.mp hi).2)
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hy
  have hxi := Finset.mem_product.mp hi
  have hyj := Finset.mem_product.mp hj
  have ho₁ := horder i i x.1 hxi.1 x.2 hxi.2
  have ho₂ := horder j j y.1 hyj.1 y.2 hyj.2
  have hlo : x.1 ≠ y.1 := by
    intro hh
    have hhigh : x.2 = y.2 := by omega
    apply hxy
    exact Prod.ext hh hhigh
  have hhi : x.2 ≠ y.2 := by
    intro hh
    apply hlo
    omega
  exact ⟨⟨x.1, y.1, x.2, y.2⟩, ⟨i, hxi.1, hxi.2⟩, ⟨j, hyj.1, hyj.2⟩,
    hlo, hhi, ho₁, ho₂, horder i j x.1 hxi.1 y.2 hyj.2,
    horder j i y.1 hyj.1 x.2 hxi.2, heq⟩

end
end Sude
