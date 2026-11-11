import Sude.FWSeedRectangleOrientation

/-! The two oriented pairs in each seed rectangle have cancelling signed
line incidence. This is geometric only; it gives no diagonal or mean bound. -/
namespace Sude
noncomputable section
open scoped BigOperators
set_option maxRecDepth 8192

/-- Each rectangle pair lies wholly on one row. -/
theorem fw_seed_rectangle_pair_row_orientation_zero {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (j : Fin 16) (rect : Fin (4 * 6)) (pair : Fin 2) (r : Fin n) :
    physicalPairLineOrientation (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
      (fun x => x.1 = r)
      (j, prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair)) = 0 := by
  classical
  unfold physicalPairLineOrientation
  rw [fw_seed_existing_rectangle_cell, fw_seed_existing_rectangle_cell]
  fin_cases pair <;> simp [prefixPairCorner, packedRectangleCorner]

/-- The two rectangle pairs have opposite signed incidence on each column. -/
theorem fw_seed_rectangle_pairs_column_orientation_zero {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (j : Fin 16) (rect : Fin (4 * 6)) (c : Fin n) :
    (∑ pair : Fin 2,
      physicalPairLineOrientation (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun x => x.2 = c)
        (j, prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair))) = 0 := by
  classical
  rw [Fin.sum_univ_two]
  unfold physicalPairLineOrientation
  rw [fw_seed_existing_rectangle_cell, fw_seed_existing_rectangle_cell,
    fw_seed_existing_rectangle_cell, fw_seed_existing_rectangle_cell]
  simp [prefixPairCorner, packedRectangleCorner]

/-- Every actual seed rectangle contributes zero signed orientation to a
row, so the complete seed-rectangle row orientation sum is zero. -/
theorem fw_seed_rectangle_row_orientation_sum_zero {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3) (r : Fin n) :
    (∑ j : Fin 16, ∑ x : Fin (4 * 6) × Fin 2,
      physicalPairLineOrientation (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun x => x.1 = r) (j, prefixDiagonalPairIndex
          (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) x)) = 0 := by
  simp only [Fintype.sum_prod_type, fw_seed_rectangle_pair_row_orientation_zero, Finset.sum_const_zero]

/-- The two oppositely oriented rectangle pairs cancel in every column. -/
theorem fw_seed_rectangle_column_orientation_sum_zero {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3) (c : Fin n) :
    (∑ j : Fin 16, ∑ rect : Fin (4 * 6), ∑ pair : Fin 2,
      physicalPairLineOrientation (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun x => x.2 = c) (j, prefixDiagonalPairIndex
          (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair))) = 0 := by
  simp only [fw_seed_rectangle_pairs_column_orientation_zero, Finset.sum_const_zero]

end
end Sude
