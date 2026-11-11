import Sude.FWGrowthFullDiagonalWeights
import Sude.FWSeedDiagonalOrientation

/-! Signed diagonal orientation for every actual growth-stage pair slot. -/
namespace Sude
noncomputable section

/-- The low endpoint is the only endpoint of a rectangle pair that may lie
on either main diagonal. Thus its orientation is minus its physical weight. -/
theorem fw_growth_rectangle_diagonal_orientation {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P*3) (hc : cols.length = P*3)
    (j : Fin P) (rect : Fin (4*6)) (pair : Fin 2) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    let idx := (j, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (rect,pair))
    physicalPairLineOrientation cells (fun c => c ∈ mainCells n) idx =
      -physicalPairLineWeight cells (fun c => c ∈ mainCells n) idx ∧
    physicalPairLineOrientation cells (fun c => c ∈ antiCells n) idx =
      -physicalPairLineWeight cells (fun c => c ∈ antiCells n) idx := by
  classical
  dsimp only
  have hm := fw_seed_rectangle_main_orientation_eq_neg_weight hs hL choice
    (btGrowingOffsetRectangle offset hoff (finProdFinEquiv (j,rect))) pair
  have ha := fw_seed_rectangle_anti_orientation_eq_neg_weight hs hL choice
    (btGrowingOffsetRectangle offset hoff (finProdFinEquiv (j,rect))) pair
  constructor <;> unfold physicalPairLineOrientation physicalPairLineWeight <;>
    rw [fw_growth_offset_rectangle_cell offset hoff hs choice rows cols hr hc j rect pair true,
      fw_growth_offset_rectangle_cell offset hoff hs choice rows cols hr hc j rect pair false]
  · simpa [physicalPairLineOrientation, rectanglePairWeight] using hm
  · simpa [physicalPairLineOrientation, rectanglePairWeight] using ha

/-- On either main diagonal, every actual growth pair's orientation equals
minus its weight. This includes arbitrary rectangle choices: no balanced
choice or stage-gap hypothesis is used. Ordinary endpoints avoid diagonals
under the supplied layer-packing hypotheses. -/
theorem fw_growth_full_diagonal_orientation {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = P * 3)
    (hc : cols.length = P * 3) (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows rows)
    (hcols : LayerPacking.PackedLayers reservedCols cols)
    (j : Fin P) (i : Fin (6*(n+8))) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    physicalPairLineOrientation cells (fun c => c ∈ mainCells n) (j,i) =
      -physicalPairLineWeight cells (fun c => c ∈ mainCells n) (j,i) ∧
    physicalPairLineOrientation cells (fun c => c ∈ antiCells n) (j,i) =
      -physicalPairLineWeight cells (fun c => c ∈ antiCells n) (j,i) := by
  classical
  dsimp only
  by_cases hm : i ∈ fwGrowthMainSlots n
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hm
    exact fw_growth_rectangle_diagonal_orientation offset hoff hs hL choice rows cols hr hc j
      ⟨a.val, by have := a.isLt; omega⟩ 0
  · by_cases ha : i ∈ fwGrowthAntiSlots n
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ha
      exact fw_growth_rectangle_diagonal_orientation offset hoff hs hL choice rows cols hr hc j
        ⟨a.val+12, by have := a.isLt; omega⟩ 0
    · by_cases hp : i ∈ fwGrowthPartnerSlots n
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
        exact fw_growth_rectangle_diagonal_orientation offset hoff hs hL choice rows cols hr hc j a 1
      · have ho : i ∈ fwGrowthOrdinarySlots n := by
          rw [fw_growth_ordinary_slots_eq_complement]
          simp [hm, ha, hp]
        obtain ⟨⟨tag,k,edge⟩, _, rfl⟩ := Finset.mem_image.mp ho
        have hf := fw_growth_ordinary_off_diagonals offset hoff hs choice rows cols hr hc
          reservedRows reservedCols hrows hcols j tag k edge false
        have ht := fw_growth_ordinary_off_diagonals offset hoff hs choice rows cols hr hc
          reservedRows reservedCols hrows hcols j tag k edge true
        simp [physicalPairLineOrientation, physicalPairLineWeight, hf.1, hf.2, ht.1, ht.2]

end
end Sude
