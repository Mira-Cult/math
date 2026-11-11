import Sude.RegularFactorSortedPlacement
import Sude.RegularBlockBalance
import Sude.CentralStock
import Sude.CentralPhysicalPlacement

/-! Ordered block estimates for the actual finite unused pool. -/
namespace Sude
noncomputable section

/-- Real values in increasing pool order, total outside the finite range. -/
def sortedFactorReal {n k : ℕ} (values : Finset (pool n)) (hcard : values.card = k * n)
    (i : ℕ) : ℝ :=
  if hi : i < k * n then ((values.orderEmbOfFin hcard ⟨i, hi⟩).val : ℝ) else 0

theorem sortedFactorReal_mono {n k : ℕ} (values : Finset (pool n))
    (hcard : values.card = k * n) :
    ∀ i j, i ≤ j → j < k * n → sortedFactorReal values hcard i ≤ sortedFactorReal values hcard j := by
  intro i j hij hj
  have hi : i < k * n := lt_of_le_of_lt hij hj
  have h := (values.orderEmbOfFin hcard).monotone
    (show (⟨i, hi⟩ : Fin (k * n)) ≤ ⟨j, hj⟩ from hij)
  have hn : (values.orderEmbOfFin hcard ⟨i, hi⟩).val ≤
      (values.orderEmbOfFin hcard ⟨j, hj⟩).val := h
  simpa [sortedFactorReal, hi, hj] using (show (((values.orderEmbOfFin hcard ⟨i, hi⟩).val : ℕ) : ℝ) ≤
    ((values.orderEmbOfFin hcard ⟨j, hj⟩).val : ℕ) by exact_mod_cast hn)

theorem sortedFactorReal_block {n k : ℕ} (values : Finset (pool n))
    (hcard : values.card = k * n) (j : Fin k) (i : Fin n) :
    sortedFactorReal values hcard (j.val * n + i.val) =
      ((sortedFactorValue values hcard (j, i)).val : ℝ) := by
  have hi : j.val * n + i.val < k * n := by
    rw [← sortedFactor_index j i]
    exact (finProdFinEquiv (j, i)).isLt
  simp only [sortedFactorReal, dif_pos hi, sortedFactorValue]
  congr 2
  apply congrArg (values.orderEmbOfFin hcard)
  apply Fin.ext
  change j.val * n + i.val = (finProdFinEquiv (j, i)).val
  exact (sortedFactor_index j i).symm

/-- Summing the consecutive sorted blocks recovers the full actual stock
sum, with no entry omitted or repeated. -/
theorem sortedFactorReal_sum {n k : ℕ} (values : Finset (pool n))
    (hcard : values.card = k * n) :
    (∑ j ∈ Finset.range k, ∑ i ∈ Finset.range n,
      sortedFactorReal values hcard (j * n + i)) =
        ∑ v ∈ values, centralPoolValue v := by
  classical
  have hsum : (∑ x : Fin k × Fin n, centralPoolValue (sortedFactorValue values hcard x)) =
      ∑ v ∈ values, centralPoolValue v := by
    have h₁ := (finProdFinEquiv : Fin k × Fin n ≃ Fin (k * n)).sum_comp
      (fun i => centralPoolValue (values.orderEmbOfFin hcard i))
    have h₂ := Finset.sum_image (f := centralPoolValue)
      (s := (Finset.univ : Finset (Fin (k * n))))
      (values.orderEmbOfFin hcard).injective.injOn
    have himage : (Finset.univ : Finset (Fin (k * n))).image (values.orderEmbOfFin hcard) = values :=
      Finset.image_orderEmbOfFin_univ values hcard
    rw [himage] at h₂
    simpa [sortedFactorValue] using h₁.trans h₂.symm
  rw [Fintype.sum_prod_type] at hsum
  rw [← hsum]
  rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ i ∈ Finset.range n,
    sortedFactorReal values hcard (j * n + i)) k]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Fin.sum_univ_eq_sum_range (fun i => sortedFactorReal values hcard (j.val * n + i)) n]
  apply Finset.sum_congr rfl
  intro i _
  exact sortedFactorReal_block values hcard j i

/-- One entry from every consecutive sorted block stays within the stock's
full range of `k` times the actual stock mean. -/
theorem sortedFactor_blocks_balanced {n k : ℕ} (values : Finset (pool n))
    (hcard : values.card = k * n) (hk : 0 < k) (hn : 0 < n) (pick : ℕ → ℝ)
    (hpick : ∀ j < k, ∃ i < n, pick j = sortedFactorReal values hcard (j * n + i)) :
    |(∑ j ∈ Finset.range k, pick j) - (k : ℝ) * centralEntriesMean values centralPoolValue| ≤
      sortedFactorReal values hcard (k * n - 1) - sortedFactorReal values hcard 0 := by
  have h := consecutive_sorted_blocks_balanced (sortedFactorReal values hcard) pick k n hk hn
    (sortedFactorReal_mono values hcard) hpick
  rw [sortedFactorReal_sum values hcard] at h
  simpa [centralEntriesMean, hcard] using h

end
end Sude
