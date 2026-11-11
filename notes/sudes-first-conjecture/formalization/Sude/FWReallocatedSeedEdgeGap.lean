import Sude.FWSeedOffsetActualRowColumn
import Sude.FWPhysicalEdgeWitnessGrid

/-! Reallocated seed-slot gaps on the corresponding physical graph edges.
No endpoint availability, allocation or invoice claim is made. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- A supplied gap-two equation for each actual seed pair slot implies the
same equation for both ordinary graph networks at every seed stage and edge. -/
theorem fw_reallocated_seed_edge_gap {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (b : Cell n ≃ Fin (n*n))
    (hgap : ∀ j i,
      entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i), true)) =
      entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i), false)) + 2)
    (edge : Fin 3 × Fin n) (network : Bool) (j : Fin 16) :
    entry b (fwSeedEdgeCells sr sc hsr hsc edge network j true) =
      entry b (fwSeedEdgeCells sr sc hsr hsc edge network j false) + 2 := by
  cases edge with
  | mk k e =>
    cases network
    · have h := hgap j (prefixOrdinaryPairIndex
        (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (0, k, e))
      rw [fw_seed_existing_row_cell, fw_seed_existing_row_cell] at h
      simpa [fwSeedEdgeCells, fwSeedOrdinaryCells, prefixStageLayer,
        bridgeStageLayerIndex, LayerPacking.sequenceCell, LayerPacking.layerCell] using h
    · have h := hgap j (prefixOrdinaryPairIndex
        (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (1, k, e))
      rw [fw_seed_existing_column_cell, fw_seed_existing_column_cell] at h
      simpa [fwSeedEdgeCells, fwSeedOrdinaryCells, prefixStageLayer,
        bridgeStageLayerIndex, LayerPacking.sequenceCell, LayerPacking.layerCell] using h

end
end Sude
