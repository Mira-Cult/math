import Sude.DiagonalLineTransfer
import Sude.LayerSequence

/-! Assemble the line-load bounds after central diagonals are reserved. -/
namespace Sude
noncomputable section

/-- A balanced ordinary support, bounded exceptional support, and the actual
unreserved diagonal cells have the RF3 line loads. No disjointness is
assumed between ordinary and exceptional supports; overlap can only lower
the upper count. -/
theorem post_diagonal_balanced_occupancy {n r₀ b : ℕ}
    (ordinary extra : Finset (Cell n))
    (hrow : ∀ i, (LayerPacking.rowUsed ordinary i).card = r₀)
    (hcol : ∀ i, (LayerPacking.colUsed ordinary i).card = r₀)
    (herow : ∀ i, (LayerPacking.rowUsed extra i).card ≤ 6 * b + 2)
    (hecol : ∀ i, (LayerPacking.colUsed extra i).card ≤ 6 * b + 2) :
    let reserved := ordinary ∪ extra
    let final := reserved ∪ unreservedDiagonalCells reserved
    (∀ i, r₀ ≤ (LayerPacking.rowUsed final i).card ∧
      (LayerPacking.rowUsed final i).card ≤ r₀ + (6 * b + 4)) ∧
    (∀ i, r₀ ≤ (LayerPacking.colUsed final i).card ∧
      (LayerPacking.colUsed final i).card ≤ r₀ + (6 * b + 4)) := by
  dsimp
  constructor
  · intro i
    let reserved := ordinary ∪ extra
    let D := unreservedDiagonalCells reserved
    change r₀ ≤ (LayerPacking.rowUsed (reserved ∪ D) i).card ∧
      (LayerPacking.rowUsed (reserved ∪ D) i).card ≤ r₀ + (6 * b + 4)
    have hsub : LayerPacking.rowUsed ordinary i ⊆ LayerPacking.rowUsed (reserved ∪ D) i := by
      intro j hj
      have hm : (i, j) ∈ ordinary := by simpa [LayerPacking.rowUsed] using hj
      have hm' : (i, j) ∈ reserved ∪ D := Finset.mem_union_left _ (Finset.mem_union_left _ hm)
      simpa [LayerPacking.rowUsed] using hm'
    have hlo := Finset.card_le_card hsub
    have hfirst : (LayerPacking.rowUsed reserved i).card ≤
        (LayerPacking.rowUsed ordinary i).card + (LayerPacking.rowUsed extra i).card := by
      rw [LayerPacking.rowUsed_union]
      exact Finset.card_union_le _ _
    have hsecond : (LayerPacking.rowUsed (reserved ∪ D) i).card ≤
        (LayerPacking.rowUsed reserved i).card + (LayerPacking.rowUsed D i).card := by
      rw [LayerPacking.rowUsed_union]
      exact Finset.card_union_le _ _
    have hd : (LayerPacking.rowUsed D i).card ≤ 2 := by
      rw [← factor_row_cells_card]
      exact row_unreserved_diagonal_card_le_two reserved i
    have ho := hrow i
    have he := herow i
    omega
  · intro i
    let reserved := ordinary ∪ extra
    let D := unreservedDiagonalCells reserved
    change r₀ ≤ (LayerPacking.colUsed (reserved ∪ D) i).card ∧
      (LayerPacking.colUsed (reserved ∪ D) i).card ≤ r₀ + (6 * b + 4)
    have hsub : LayerPacking.colUsed ordinary i ⊆ LayerPacking.colUsed (reserved ∪ D) i := by
      intro j hj
      have hm : (j, i) ∈ ordinary := by simpa [LayerPacking.colUsed] using hj
      have hm' : (j, i) ∈ reserved ∪ D := Finset.mem_union_left _ (Finset.mem_union_left _ hm)
      simpa [LayerPacking.colUsed] using hm'
    have hlo := Finset.card_le_card hsub
    have hfirst : (LayerPacking.colUsed reserved i).card ≤
        (LayerPacking.colUsed ordinary i).card + (LayerPacking.colUsed extra i).card := by
      rw [LayerPacking.colUsed_union]
      exact Finset.card_union_le _ _
    have hsecond : (LayerPacking.colUsed (reserved ∪ D) i).card ≤
        (LayerPacking.colUsed reserved i).card + (LayerPacking.colUsed D i).card := by
      rw [LayerPacking.colUsed_union]
      exact Finset.card_union_le _ _
    have hd : (LayerPacking.colUsed D i).card ≤ 2 := by
      rw [← factor_column_cells_card]
      exact column_unreserved_diagonal_card_le_two reserved i
    have ho := hcol i
    have he := hecol i
    omega

/-- A physically packed ordinary layer family has exactly two cells per
layer in every row and column. -/
theorem packed_layers_exact_occupancy {n : ℕ} {base : Finset (Cell n)}
    {layers : List (LayerPacking.Layer n)} (h : LayerPacking.PackedLayers base layers) :
    (∀ i, (LayerPacking.rowUsed (LayerPacking.layersSupport layers) i).card = 2 * layers.length) ∧
    (∀ i, (LayerPacking.colUsed (LayerPacking.layersSupport layers) i).card = 2 * layers.length) := by
  constructor
  · intro i
    rw [LayerPacking.rowUsed_card_eq]
    exact h.row_balance i
  · intro i
    rw [LayerPacking.colUsed_card_eq]
    exact h.column_balance i

/-- The RF3 line-load hypotheses follow for an actually packed ordinary
layer family, once the exceptional supports meet their explicit line budgets. -/
theorem packed_layers_post_diagonal_occupancy {n b : ℕ} {base : Finset (Cell n)}
    {layers : List (LayerPacking.Layer n)} (h : LayerPacking.PackedLayers base layers)
    (extra : Finset (Cell n))
    (herow : ∀ i, (LayerPacking.rowUsed extra i).card ≤ 6 * b + 2)
    (hecol : ∀ i, (LayerPacking.colUsed extra i).card ≤ 6 * b + 2) :
    let reserved := LayerPacking.layersSupport layers ∪ extra
    let final := reserved ∪ unreservedDiagonalCells reserved
    (∀ i, 2 * layers.length ≤ (LayerPacking.rowUsed final i).card ∧
      (LayerPacking.rowUsed final i).card ≤ 2 * layers.length + (6 * b + 4)) ∧
    (∀ i, 2 * layers.length ≤ (LayerPacking.colUsed final i).card ∧
      (LayerPacking.colUsed final i).card ≤ 2 * layers.length + (6 * b + 4)) := by
  have hbalance := packed_layers_exact_occupancy h
  exact post_diagonal_balanced_occupancy (b := b) (LayerPacking.layersSupport layers) extra
    hbalance.1 hbalance.2 herow hecol

end
end Sude
