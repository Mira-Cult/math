import Sude.FWBridgeFivePlacement
import Sude.FWPermutationExpander
import Sude.BridgePhysicalGrid
import Sude.FWSeedQuota

/-! FW bridge placement and conditional seed selection sharing the same batches. -/
namespace Sude
noncomputable section

/-- Select a common FW-expanding graph, five placed bridge batches, and
retained seeds against those same batches. The arbitrary joint rectangle count
is explicit; seed quota and seed/bridge physical coexistence are not proved. -/
theorem bmor_fw_bridge_placement_and_quota_seeds
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (n L : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (otherChoice : Fin L → Bool) (a : Cell n ≃ Fin (n * n))
    (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    ∃ p : Fin 3 → Equiv.Perm (Fin n),
      (∀ i v, p i v ≠ v) ∧
      (∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
        500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card) ∧
    ∃ (batches : ℕ → List DoublePair)
      (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j),
      (∀ i < 5, ∀ j < 5, i ≠ j →
        Disjoint (doubleBatchLow (batches i) ∪ doubleBatchHigh (batches i))
          (doubleBatchLow (batches j) ∪ doubleBatchHigh (batches j))) ∧
      (∀ j ≤ 5, (priorBridgeReservation ∅ (Finset.range j) batches).card ≤
        (∅ : Finset ℕ).card + j * (4 * (3 * (n + 8)))) ∧
      (∀ p ∈ priorBridgeReservation ∅ (Finset.range 5) batches,
        p ∈ poolFinset n ∧ poolMaximum n ≤ 4 * p) ∧
      (let Q := 6 * (n + 8)
       let r := 16 + 2 - 1
       ∃ (candidates : Finset ℕ) (hcard : candidates.card = r * Q),
         candidates ⊆ seeds ∧
         ∃ (kept : Finset ℕ) (hsub : kept ⊆ Finset.range r), kept.card = 16 ∧
           (let w := sortedSeedReal candidates r Q hcard
            ∃ z : ℝ, (∃ i ∈ kept, z = w (i * Q + (Q - 1)) - w (i * Q)) ∧
             (∀ i ∈ kept, w (i * Q + (Q - 1)) - w (i * Q) ≤ z) ∧
             3 * 6 * (∑ i ∈ kept, (w (i * Q + (Q - 1)) - w (i * Q)) ^ 2) + 4 * z ^ 2 ≤
               (11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2) ∧
           (let B := priorBridgeReservation ∅ (Finset.range 5) batches
            let R := retainedSeedEndpoints candidates r Q 2 hcard kept hsub
            R.card = 2 * Q * 16 ∧ R ⊆ poolFinset n \ B ∧
            ∀ x, x.1.1.val ∉ kept →
              sortedSeedEndpoint candidates r Q 2 hcard x ∈ poolFinset n \ (B ∪ R))) ∧
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
  obtain ⟨p, hderange, hexp⟩ := fw_permutation_expander_exists hnlo
  have hlen : (bridgeRepeatedPermutations 5 p).length = 15 := by
    simpa using (bridgeRepeatedPermutations_length (J := 5) p)
  have hder : ∀ π ∈ bridgeRepeatedPermutations 5 p, ∀ i, π i ≠ i :=
    bridgeRepeatedPermutations_derange p hderange
  obtain ⟨batches, hvalid, hdisjoint, hbudget, rows, cols, hr, hc, a', hrmap, hcmap,
    hrpacked, hcpacked, hinj, hfree, hdiag, hord, hdiagGap, hordGap⟩ :=
    bmor_fw_five_bridge_packed_placement bmor upper lower n L hnlo hnhi
      hrect hs otherChoice a (bridgeRepeatedPermutations 5 p)
      (bridgeRepeatedPermutations 5 p) hlen hlen hder hder
  have hbridge := fw_selected_bridge_values_pool_and_quarter bmor upper n batches
    (by omega) (by omega) hvalid
  obtain ⟨candidates, hcard, hcand, kept, hsub, hkept, hvariance, hreservation⟩ :=
    fw_actual_narrow_seed_reservation_of_quota lower n seeds
      (priorBridgeReservation ∅ (Finset.range 5) batches) hnlo hnhi hseed hprime
      (fun p hp => (hbridge p hp).2) hcount
  exact ⟨p, hderange, hexp, batches, hvalid, hdisjoint, hbudget, hbridge,
    ⟨candidates, hcard, hcand, kept, hsub, hkept, hvariance, hreservation⟩,
    rows, cols, hr, hc, a',
    hrmap, hcmap, hrpacked, hcpacked, hinj, hfree, hdiag, hord, hdiagGap, hordGap⟩

end
end Sude
