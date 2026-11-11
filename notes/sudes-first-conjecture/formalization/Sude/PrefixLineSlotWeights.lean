import Sude.PrefixPhysicalSlotGeometry
import Sude.PhysicalSlotNonnegative

/-! Match physical line-incidence weights to the allocator's actual slots. -/
namespace Sude
noncomputable section

/-- For every physical stage label, the row probability weight is exactly
the number of its two actual cells in that row. -/
theorem prefixPairCells_row_weight_at_label {P d layers n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (j : Fin P) (r : Fin n) (tag : PrefixStagePair d layers n) :
    physicalPairLineWeight (prefixPairCells hfit hdiag hexact hrect hs choice rows cols hrows hcols)
      (fun c => c ∈ rowCells r) (j, prefixStagePairSlot hfit hdiag tag) =
    prefixStageRowIncidence hrect hs choice rows cols hrows hcols j r tag := by
  classical
  cases tag with
  | inl x =>
    rcases x with ⟨rect, pair⟩
    simp [physicalPairLineWeight, prefixStageRowIncidence, prefixStagePairSlot,
      rectanglePairWeight, prefixRectanglePairSlot, prefixPairCells_rectangle] <;>
      split_ifs <;> simp_all
  | inr x =>
    rcases x with ⟨network, layer, edge⟩
    fin_cases network
    · simp [physicalPairLineWeight, prefixStageRowIncidence, prefixStagePairSlot,
        prefixPairCells_row_network, LayerPacking.sequenceCell, prefixStageLayer,
        LayerPacking.layerRowWeight]
    · simp [physicalPairLineWeight, prefixStageRowIncidence, prefixStagePairSlot,
        prefixPairCells_column_network, LayerPacking.sequenceCell, prefixStageLayer,
        LayerPacking.layerColumnWeight]

/-- The analogous identity for every physical column. -/
theorem prefixPairCells_column_weight_at_label {P d layers n Q L : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hexact : (4 * d) * 2 + 2 * (layers * n) = Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (j : Fin P) (c : Fin n) (tag : PrefixStagePair d layers n) :
    physicalPairLineWeight (prefixPairCells hfit hdiag hexact hrect hs choice rows cols hrows hcols)
      (fun x => x ∈ columnCells c) (j, prefixStagePairSlot hfit hdiag tag) =
    prefixStageColumnIncidence hrect hs choice rows cols hrows hcols j c tag := by
  classical
  cases tag with
  | inl x =>
    rcases x with ⟨rect, pair⟩
    simp [physicalPairLineWeight, prefixStageColumnIncidence, prefixStagePairSlot,
      rectanglePairWeight, prefixRectanglePairSlot, prefixPairCells_rectangle] <;>
      split_ifs <;> simp_all
  | inr x =>
    rcases x with ⟨network, layer, edge⟩
    fin_cases network
    · simp [physicalPairLineWeight, prefixStageColumnIncidence, prefixStagePairSlot,
        prefixPairCells_row_network, LayerPacking.sequenceCell, prefixStageLayer,
        LayerPacking.layerColumnWeight]
    · simp [physicalPairLineWeight, prefixStageColumnIncidence, prefixStagePairSlot,
        prefixPairCells_column_network, LayerPacking.sequenceCell, prefixStageLayer,
        LayerPacking.layerRowWeight]

end
end Sude
