import Sude.FWBridgeLayerSlots
import Sude.FWBridgeJointPlacement

/-! Install selected FW bridge endpoints into the constructed layer geometry.
This does not assert expansion or the existence of a later controller layout. -/
namespace Sude
noncomputable section

/-- Given valid FW batches with empty initial reservation and supplied
row/column derangements, pack their physical layers around the joint RP1
rectangles and install both diagonal and ordinary endpoints in one square.
All gap equations use the actual selected FW batches. -/
theorem fw_install_bridge_on_packed_layers_empty
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n L : ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (hn : 19485 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (otherChoice : Fin L → Bool) (a : Cell n ≃ Fin (n * n))
    (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrlen : rowPerms.length = 15) (hclen : colPerms.length = 15)
    (hrderange : ∀ π ∈ rowPerms, ∀ i, π i ≠ i)
    (hcderange : ∀ π ∈ colPerms, ∀ i, π i ≠ i) :
    ∃ (rows cols : List (LayerPacking.Layer n))
      (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
      (a' : Cell n ≃ Fin (n * n)),
      rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
      LayerPacking.PackedLayers
        (packedRectangleSupport hs (bridgeDiagonalChoice hrect otherChoice)) rows ∧
      LayerPacking.PackedLayers
        (LayerPacking.transposeCells
          (packedRectangleSupport hs (bridgeDiagonalChoice hrect otherChoice) ∪
            LayerPacking.layersSupport rows)) cols ∧
      Function.Injective (fwBridgeLayerCells rows cols hr hc) ∧
      (∀ x, fwBridgeLayerCells rows cols hr hc x ∉
        packedRectangleSupport hs (bridgeDiagonalChoice hrect otherChoice)) ∧
      (∀ t side, entry a' (packedRectangleCorner hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t, side)) =
        fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeDiagonalSlot n (t, side))) ∧
      (∀ x, entry a' (fwBridgeLayerCells rows cols hr hc x) =
        fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x)) ∧
      (∀ t : Fin (5 * (4 * 6)),
        let block := (fwBridgeDiagonalSlot n (t, 0)).1
        let gap := selectedBridgeGap batches block.2 block.1
        0 < gap ∧ 2 ∣ gap ∧
        entry a' (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t),
            RectanglePacking.secondColumn hs (bridgeDiagonalChoice hrect otherChoice)
              (bridgeDiagonalRectangle hrect t)) =
          entry a' (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t),
            RectanglePacking.firstColumn hs (bridgeDiagonalChoice hrect otherChoice)
              (bridgeDiagonalRectangle hrect t)) + gap ∧
        entry a' (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t),
            RectanglePacking.firstColumn hs (bridgeDiagonalChoice hrect otherChoice)
              (bridgeDiagonalRectangle hrect t)) =
          entry a' (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t),
            RectanglePacking.secondColumn hs (bridgeDiagonalChoice hrect otherChoice)
              (bridgeDiagonalRectangle hrect t)) + gap) ∧
      (∀ (j : Fin 5) (p : Fin 3 × Fin n) (network : Bool),
        let block := (fwBridgeOrdinarySlot n ((j, p), (network, false))).1.2
        let gap := selectedBridgeGap batches block j
        0 < gap ∧ 2 ∣ gap ∧
        entry a' (fwBridgeLayerCells rows cols hr hc ((j, p), (network, true))) =
          entry a' (fwBridgeLayerCells rows cols hr hc ((j, p), (network, false))) + gap) := by
  obtain ⟨rows, cols, hr, hc, hrmap, hcmap, hrpacked, hcpacked, hinj, hfree, hcorner⟩ :=
    fw_bridge_layer_cells_exist hn hrect hs otherChoice rowPerms colPerms
      hrlen hclen hrderange hcderange
  have hreserved : ∀ c ∈ (∅ : Finset (Cell n)), entry a c ∈ (∅ : Finset ℕ) := by simp
  have hrectFree : ∀ t : Fin (5 * (4 * 6)), Disjoint
      (rectangleCells (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.firstColumn hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t))
        (RectanglePacking.secondColumn hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t))) (∅ : Finset (Cell n)) := by simp
  have hslotFree : ∀ x, fwBridgeLayerCells rows cols hr hc x ∉ (∅ : Finset (Cell n)) ∧
      ∀ t side, fwBridgeLayerCells rows cols hr hc x ≠
        packedRectangleCorner hs (bridgeDiagonalChoice hrect otherChoice)
          (bridgeDiagonalRectangle hrect t, side) := by
    intro x
    exact ⟨by simp, fun t side => hcorner x (bridgeDiagonalRectangle hrect t) side⟩
  obtain ⟨a', hdiag, hord, _, hdiagGap, hordGap⟩ :=
    fw_install_bridge_diagonals_and_ordinary bmor upper n L ∅ batches hvalid (by omega)
      hnmax hrect hs otherChoice a ∅ hreserved hrectFree (fwBridgeLayerCells rows cols hr hc)
      hinj hslotFree
  exact ⟨rows, cols, hr, hc, a', hrmap, hcmap, hrpacked, hcpacked, hinj, hfree,
    hdiag, hord, hdiagGap, hordGap⟩

end
end Sude
