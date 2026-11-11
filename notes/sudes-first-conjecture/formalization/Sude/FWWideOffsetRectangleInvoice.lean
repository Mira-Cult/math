import Sude.FWWideOffsetPairIncidence

/-! Global row and column squared-incidence bounds for the selected wide
rectangles. The ordinary network contribution is not included. -/
namespace Sude
noncomputable section

/-- The entire offset wide rectangle family contributes at most four to the
squared pair-incidence invoice of any row, with arbitrary rectangle choice. -/
theorem fw_wide_offset_row_pair_invoice {J n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + J * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) (r : Fin n) :
    (∑ x, (rectanglePairWeight hs choice (fun c => c.1 = r)
      (fwWideOffsetPairSlot hwide x)) ^ 2) ≤ 4 := by
  classical
  let w : Fin L × Fin 2 → ℝ := rectanglePairWeight hs choice (fun c => c.1 = r)
  let e := fwWideOffsetPairSlot hwide
  have hsub : Finset.univ.image e ⊆ (Finset.univ : Finset (Fin L × Fin 2)) := Finset.subset_univ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun x => (w x) ^ 2) (by intro x hx hx'; exact sq_nonneg (w x))
  rw [Finset.sum_image (by intro x _ y _ h; exact fwWideOffsetPairSlot_injective hwide h)] at hsum
  exact hsum.trans (packedRectangle_row_pair_invoice hs choice r)

/-- The entire offset wide rectangle family has the same global invoice for
any column, without any balanced diagonal-choice hypothesis. -/
theorem fw_wide_offset_column_pair_invoice {J n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + J * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) (c : Fin n) :
    (∑ x, (rectanglePairWeight hs choice (fun z => z.2 = c)
      (fwWideOffsetPairSlot hwide x)) ^ 2) ≤ 4 := by
  classical
  let w : Fin L × Fin 2 → ℝ := rectanglePairWeight hs choice (fun z => z.2 = c)
  let e := fwWideOffsetPairSlot hwide
  have hsub : Finset.univ.image e ⊆ (Finset.univ : Finset (Fin L × Fin 2)) := Finset.subset_univ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun x => (w x) ^ 2) (by intro x hx hx'; exact sq_nonneg (w x))
  rw [Finset.sum_image (by intro x _ y _ h; exact fwWideOffsetPairSlot_injective hwide h)] at hsum
  exact hsum.trans (packedRectangle_column_pair_invoice hs choice c)

/-- The row invoice in actual reindexed wide physical pair slots. The sum is
only over rectangle tags, not ordinary network slots. -/
theorem fw_wide_reindexed_rectangle_row_invoice {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (r : Fin n) :
    (∑ j : Fin (3 * (n / 450)), ∑ rect : Fin (4 * 6), ∑ pair : Fin 2,
      (physicalPairLineWeight (fwWidePhysicalPairCells hwide hs choice rows cols hr hc)
        (fun c => c.1 = r) (j, fwPrefixToControllerPair n
          (prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair)))) ^ 2) ≤ 4 := by
  classical
  simp_rw [fw_wide_reindexed_rectangle_pair_weight]
  simpa [Fintype.sum_prod_type] using fw_wide_offset_row_pair_invoice hwide hs choice r

/-- The corresponding global column invoice over rectangle tags. -/
theorem fw_wide_reindexed_rectangle_column_invoice {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (c : Fin n) :
    (∑ j : Fin (3 * (n / 450)), ∑ rect : Fin (4 * 6), ∑ pair : Fin 2,
      (physicalPairLineWeight (fwWidePhysicalPairCells hwide hs choice rows cols hr hc)
        (fun z => z.2 = c) (j, fwPrefixToControllerPair n
          (prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair)))) ^ 2) ≤ 4 := by
  classical
  simp_rw [fw_wide_reindexed_rectangle_pair_weight]
  simpa [Fintype.sum_prod_type] using fw_wide_offset_column_pair_invoice hwide hs choice c

end
end Sude
