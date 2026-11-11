import Sude.FWBridgeFiveEmpty
import Sude.FWBridgeLayerPlacement

/-! Choose the five FW bridge batches and install them in packed layers.
Expansion and compatibility with subsequent seed or controller layouts are
not asserted. -/
namespace Sude
noncomputable section

/-- In the FW range, explicit BMOR and RS inputs furnish the five selected
batches, whose actual endpoints and gaps are installed together in the
constructed geometry for the supplied derangements. -/
theorem bmor_fw_five_bridge_packed_placement
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (n L : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (otherChoice : Fin L → Bool) (a : Cell n ≃ Fin (n * n))
    (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrlen : rowPerms.length = 15) (hclen : colPerms.length = 15)
    (hrderange : ∀ π ∈ rowPerms, ∀ i, π i ≠ i)
    (hcderange : ∀ π ∈ colPerms, ∀ i, π i ≠ i) :
    ∃ (batches : ℕ → List DoublePair)
      (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j),
      (∀ i < 5, ∀ j < 5, i ≠ j →
        Disjoint (doubleBatchLow (batches i) ∪ doubleBatchHigh (batches i))
          (doubleBatchLow (batches j) ∪ doubleBatchHigh (batches j))) ∧
      (∀ j ≤ 5, (priorBridgeReservation ∅ (Finset.range j) batches).card ≤
        (∅ : Finset ℕ).card + j * (4 * (3 * (n + 8)))) ∧
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
  obtain ⟨batches, hvalid, hdisjoint, hbudget⟩ :=
    bmor_fw_five_bridge_batches_empty bmor upper lower hnlo hnhi
  obtain ⟨rows, cols, hr, hc, a', hrmap, hcmap, hrpacked, hcpacked, hinj, hfree,
      hdiag, hord, hdiagGap, hordGap⟩ :=
    fw_install_bridge_on_packed_layers_empty bmor upper n L batches hvalid hnlo (by omega)
      hrect hs otherChoice a rowPerms colPerms hrlen hclen hrderange hcderange
  exact ⟨batches, hvalid, hdisjoint, hbudget, rows, cols, hr, hc, a', hrmap, hcmap,
    hrpacked, hcpacked, hinj, hfree, hdiag, hord, hdiagGap, hordGap⟩

end
end Sude
