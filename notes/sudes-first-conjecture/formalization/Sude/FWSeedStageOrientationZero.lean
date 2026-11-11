import Sude.FWGrowthStageOrientationZero
import Sude.FWSeedExistingReallocation

/-! The actual ordered seed cells have zero signed orientation in each
row and column. Entry switches leave this fixed map unchanged but may
invalidate the ordered signed-gap premise needed for physical cancellation. -/
namespace Sude
noncomputable section

/-- The seed role map is the same exact-capacity offset pair map. -/
theorem fw_seed_existing_pair_cells_eq_offset {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3) :
    fwSeedExistingPairCells hseed hs choice sr sc hsr hsc =
      btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
        (5 * (4 * 6)) hseed hs choice sr sc hsr hsc := by
  rfl

/-- Every complete ordered seed stage has zero net orientation on each row. -/
theorem fw_seed_stage_row_orientation_zero {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3) (j : Fin 16) (r : Fin n) :
    (∑ q : Fin (6 * (n + 8)), physicalPairLineOrientation
      (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) (fun z => z.1 = r) (j,q)) = 0 := by
  rw [fw_seed_existing_pair_cells_eq_offset]
  exact fw_growth_stage_row_orientation_zero (5 * (4 * 6)) hseed hs choice sr sc hsr hsc j r

/-- Every complete ordered seed stage has zero net orientation on each column. -/
theorem fw_seed_stage_column_orientation_zero {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3) (j : Fin 16) (c : Fin n) :
    (∑ q : Fin (6 * (n + 8)), physicalPairLineOrientation
      (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) (fun z => z.2 = c) (j,q)) = 0 := by
  rw [fw_seed_existing_pair_cells_eq_offset]
  exact fw_growth_stage_column_orientation_zero (5 * (4 * 6)) hseed hs choice sr sc hsr hsc j c


/-- Summing all ordered seed stages leaves zero row orientation. -/
theorem fw_seed_row_orientation_sum_zero {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3) (r : Fin n) :
    (∑ p : Fin 16 × Fin (6 * (n + 8)), physicalPairLineOrientation
      (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) (fun z => z.1 = r) p) = 0 := by
  rw [Fintype.sum_prod_type]
  simp only [fw_seed_stage_row_orientation_zero hseed hs choice sr sc hsr hsc, Finset.sum_const_zero]

/-- Summing all ordered seed stages leaves zero column orientation. -/
theorem fw_seed_column_orientation_sum_zero {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3) (c : Fin n) :
    (∑ p : Fin 16 × Fin (6 * (n + 8)), physicalPairLineOrientation
      (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) (fun z => z.2 = c) p) = 0 := by
  rw [Fintype.sum_prod_type]
  simp only [fw_seed_stage_column_orientation_zero hseed hs choice sr sc hsr hsc, Finset.sum_const_zero]


/-- A supplied seed deviation invoice loses its ordered row-orientation term. -/
theorem fw_seed_row_deviation_without_orientation {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (a : Cell n ≃ Fin (n*n)) (M B : ℝ) (r : Fin n)
    (hbound : let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      |(∑ c ∈ (Finset.univ.image cells).filter (fun z => z.1 = r), (entry a c : ℝ)) - M -
        (∑ p, physicalPairLineOrientation cells (fun z => z.1 = r) p * ((2 : ℝ) / 2))| ≤ B) :
    let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    |(∑ c ∈ (Finset.univ.image cells).filter (fun z => z.1 = r), (entry a c : ℝ)) - M| ≤ B := by
  dsimp only at hbound ⊢
  have hz : (∑ p : Fin 16 × Fin (6 * (n + 8)),
      physicalPairLineOrientation (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun z => z.1 = r) p * ((2 : ℝ) / 2)) = 0 := by
    rw [← Finset.sum_mul, fw_seed_row_orientation_sum_zero hseed hs choice sr sc hsr hsc r]
    ring
  simpa only [hz, sub_zero] using hbound

/-- A supplied seed deviation invoice loses its ordered column-orientation term. -/
theorem fw_seed_column_deviation_without_orientation {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (a : Cell n ≃ Fin (n*n)) (M B : ℝ) (c : Fin n)
    (hbound : let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      |(∑ z ∈ (Finset.univ.image cells).filter (fun z => z.2 = c), (entry a z : ℝ)) - M -
        (∑ p, physicalPairLineOrientation cells (fun z => z.2 = c) p * ((2 : ℝ) / 2))| ≤ B) :
    let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    |(∑ z ∈ (Finset.univ.image cells).filter (fun z => z.2 = c), (entry a z : ℝ)) - M| ≤ B := by
  dsimp only at hbound ⊢
  have hz : (∑ p : Fin 16 × Fin (6 * (n + 8)),
      physicalPairLineOrientation (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun z => z.2 = c) p * ((2 : ℝ) / 2)) = 0 := by
    rw [← Finset.sum_mul, fw_seed_column_orientation_sum_zero hseed hs choice sr sc hsr hsc c]
    ring
  simpa only [hz, sub_zero] using hbound

end
end Sude
