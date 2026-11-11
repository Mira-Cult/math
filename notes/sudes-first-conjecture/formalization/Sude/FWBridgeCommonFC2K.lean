import Sude.FWBridgeFivePlacement
import Sude.PermutationExceptions
import Sude.BridgePhysicalGrid

/-! Bridge-only FW placement using a proved common derangement triple. -/
namespace Sude
noncomputable section

/-- The five FW bridge stages admit an isolated `L=120` placement with
both ordinary networks using the same three derangements at every stage.
The exposed `199/200` cut bound is the FC2K bound; it does not establish
FW6's stronger `519/500` expansion or the later controller geometry. -/
theorem bmor_fw_bridge_placement_with_common_fc2k_graph
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (n : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (otherChoice : Fin 120 → Bool) (a : Cell n ≃ Fin (n * n)) :
    let hrect : 5 * (4 * 6) ≤ 120 := by decide
    let hs : 2 * 120 + 1 ≤ n := by omega
    ∃ p : Fin 3 → Equiv.Perm (Fin n),
      (∀ i v, p i v ≠ v) ∧
      (∀ S : Finset (Fin n), 199 * min S.card (n - S.card) ≤
        200 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card) ∧
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
      rows.map Prod.fst = (bridgeRepeatedPermutations 5 p) ∧ cols.map Prod.fst = (bridgeRepeatedPermutations 5 p) ∧
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
  dsimp only
  obtain ⟨p, hderange, hexp⟩ := fc2k_permutation_expander_exists (show 2001 ≤ n by omega)
  have hlen : (bridgeRepeatedPermutations 5 p).length = 15 := by
    simpa using (bridgeRepeatedPermutations_length (J := 5) p)
  have hder : ∀ π ∈ bridgeRepeatedPermutations 5 p, ∀ i, π i ≠ i :=
    bridgeRepeatedPermutations_derange p hderange
  obtain ⟨batches, hvalid, hdisjoint, hbudget, rows, cols, hr, hc, a', hrmap, hcmap,
    hrpacked, hcpacked, hinj, hfree, hdiag, hord, hdiagGap, hordGap⟩ :=
    bmor_fw_five_bridge_packed_placement bmor upper lower n 120 hnlo hnhi
      (by decide) (by omega) otherChoice a (bridgeRepeatedPermutations 5 p)
      (bridgeRepeatedPermutations 5 p) hlen hlen hder hder
  exact ⟨p, hderange, hexp, batches, hvalid, hdisjoint, hbudget, rows, cols, hr, hc, a',
    hrmap, hcmap, hrpacked, hcpacked, hinj, hfree, hdiag, hord, hdiagGap, hordGap⟩

end
end Sude
