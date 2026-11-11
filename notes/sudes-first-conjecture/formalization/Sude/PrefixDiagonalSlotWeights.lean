import Sude.PrefixLineSlotWeights
import Sude.DiagonalPhysicalInvoice

/-! Match both diagonal slot weights to the actual prefix cells. -/
namespace Sude
noncomputable section

/-- Actual row-network slot endpoints avoid both diagonals. -/
theorem prefixPairCells_row_network_off_diagonals {P d layers n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (reserved : Finset (Cell n))
    (packed : LayerPacking.PackedLayers reserved rows)
    (j : Fin P) (k : Fin layers) (edge : Fin n) (side : Bool) :
    prefixPairCells hfit hdiag hexact hrect hs choice rows cols hrows hcols
      ((j, prefixOrdinaryPairIndex hfit (0, k, edge)), side) ∉ mainCells n ∧
    prefixPairCells hfit hdiag hexact hrect hs choice rows cols hrows hcols
      ((j, prefixOrdinaryPairIndex hfit (0, k, edge)), side) ∉ antiCells n := by
  rw [prefixPairCells_row_network, prefixStageLayer_sequenceCell]
  exact prefixStageLayer_off_diagonals rows hrows reserved packed j k edge side

/-- Actual transposed column-network slot endpoints avoid both diagonals. -/
theorem prefixPairCells_column_network_off_diagonals {P d layers n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (reserved : Finset (Cell n))
    (packed : LayerPacking.PackedLayers reserved cols)
    (j : Fin P) (k : Fin layers) (edge : Fin n) (side : Bool) :
    prefixPairCells hfit hdiag hexact hrect hs choice rows cols hrows hcols
      ((j, prefixOrdinaryPairIndex hfit (1, k, edge)), side) ∉ mainCells n ∧
    prefixPairCells hfit hdiag hexact hrect hs choice rows cols hrows hcols
      ((j, prefixOrdinaryPairIndex hfit (1, k, edge)), side) ∉ antiCells n := by
  rw [prefixPairCells_column_network, prefixStageLayer_sequenceCell]
  exact prefixStageLayer_swap_off_diagonals cols hcols reserved packed j k edge side

/-- For each physical pair label, the main-diagonal incidence weight is the
number of its actual endpoints on that diagonal. -/
theorem prefixPairCells_main_weight_at_label {P d layers n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows rows)
    (packedCols : LayerPacking.PackedLayers reservedCols cols)
    (j : Fin P) (tag : PrefixStagePair d layers n) :
    physicalPairLineWeight (prefixPairCells hfit hdiag hexact hrect hs choice rows cols hrows hcols)
      (fun c => c ∈ mainCells n) (j, prefixStagePairSlot hfit hdiag tag) =
    prefixStageDiagonalIncidence hrect hs choice (fun c => c ∈ mainCells n) j tag := by
  classical
  cases tag with
  | inl x =>
    rcases x with ⟨rect, pair⟩
    simp [physicalPairLineWeight, prefixStageDiagonalIncidence, prefixStagePairSlot,
      rectanglePairWeight, prefixRectanglePairSlot, prefixPairCells_rectangle] <;>
      split_ifs <;> simp_all
  | inr x =>
    rcases x with ⟨network, layer, edge⟩
    fin_cases network
    · have hf := (prefixPairCells_row_network_off_diagonals hfit hdiag hexact hrect hs choice rows cols hrows hcols
        reservedRows packedRows j layer edge false).1
      have ht := (prefixPairCells_row_network_off_diagonals hfit hdiag hexact hrect hs choice rows cols hrows hcols
        reservedRows packedRows j layer edge true).1
      simp [prefixStagePairSlot, prefixStageDiagonalIncidence, physicalPairLineWeight, hf, ht]
    · have hf := (prefixPairCells_column_network_off_diagonals hfit hdiag hexact hrect hs choice rows cols hrows hcols
        reservedCols packedCols j layer edge false).1
      have ht := (prefixPairCells_column_network_off_diagonals hfit hdiag hexact hrect hs choice rows cols hrows hcols
        reservedCols packedCols j layer edge true).1
      simp [prefixStagePairSlot, prefixStageDiagonalIncidence, physicalPairLineWeight, hf, ht]

/-- The corresponding identity for the antidiagonal. -/
theorem prefixPairCells_anti_weight_at_label {P d layers n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows rows)
    (packedCols : LayerPacking.PackedLayers reservedCols cols)
    (j : Fin P) (tag : PrefixStagePair d layers n) :
    physicalPairLineWeight (prefixPairCells hfit hdiag hexact hrect hs choice rows cols hrows hcols)
      (fun c => c ∈ antiCells n) (j, prefixStagePairSlot hfit hdiag tag) =
    prefixStageDiagonalIncidence hrect hs choice (fun c => c ∈ antiCells n) j tag := by
  classical
  cases tag with
  | inl x =>
    rcases x with ⟨rect, pair⟩
    simp [physicalPairLineWeight, prefixStageDiagonalIncidence, prefixStagePairSlot,
      rectanglePairWeight, prefixRectanglePairSlot, prefixPairCells_rectangle] <;>
      split_ifs <;> simp_all
  | inr x =>
    rcases x with ⟨network, layer, edge⟩
    fin_cases network
    · have hf := (prefixPairCells_row_network_off_diagonals hfit hdiag hexact hrect hs choice rows cols hrows hcols
        reservedRows packedRows j layer edge false).2
      have ht := (prefixPairCells_row_network_off_diagonals hfit hdiag hexact hrect hs choice rows cols hrows hcols
        reservedRows packedRows j layer edge true).2
      simp [prefixStagePairSlot, prefixStageDiagonalIncidence, physicalPairLineWeight, hf, ht]
    · have hf := (prefixPairCells_column_network_off_diagonals hfit hdiag hexact hrect hs choice rows cols hrows hcols
        reservedCols packedCols j layer edge false).2
      have ht := (prefixPairCells_column_network_off_diagonals hfit hdiag hexact hrect hs choice rows cols hrows hcols
        reservedCols packedCols j layer edge true).2
      simp [prefixStagePairSlot, prefixStageDiagonalIncidence, physicalPairLineWeight, hf, ht]

end
end Sude
