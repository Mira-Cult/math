import Sude.FWBridgeSeedFullPlacement
import Sude.FWPhysicalProtectedValues

/-! Reserve and install wide FW endpoints without moving the selected bridge
and retained seed endpoints. Wide cells are arbitrary, not FW layout. -/
namespace Sude
noncomputable section
set_option maxRecDepth 8192

/-- Using the actual pool mean and its explicit interval bounds, select the
FW wide blocks after the selected bridge and seed populations and preserve
their actual installed cells. Wide-cell rectangle/network geometry, future
growth, and the complete controller are not asserted. -/
theorem bmor_fw_bridge_seed_and_wide_protected
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp)
    (n L : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hmlo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤
      (Lucas.poolTotal n : ℝ) / (n * n : ℕ))
    (hmhi : (Lucas.poolTotal n : ℝ) / (n * n : ℕ) ≤
      (123 / 250 : ℝ) * (poolMaximum n : ℝ))
    (hrect : 5 * (4 * 6) ≤ L) (hseedrect : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (otherChoice : Fin L → Bool)
    (a : Cell n ≃ Fin (n * n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    let choice := fwBridgeSeedRectangleChoice hrect hseedrect otherChoice
    let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
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
    ∃ (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8))),
      candidates ⊆ seeds ∧
    ∃ (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16),
      (let w := sortedSeedReal candidates 17 (6 * (n + 8)) hcard
       ∃ z : ℝ, (∃ i ∈ kept, z = w (i * (6 * (n + 8)) + (6 * (n + 8) - 1)) - w (i * (6 * (n + 8)))) ∧
        (∀ i ∈ kept, w (i * (6 * (n + 8)) + (6 * (n + 8) - 1)) - w (i * (6 * (n + 8))) ≤ z) ∧
        3 * 6 * (∑ i ∈ kept, (w (i * (6 * (n + 8)) + (6 * (n + 8) - 1)) - w (i * (6 * (n + 8)))) ^ 2) + 4 * z ^ 2 ≤
          (11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2) ∧
      Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard) ∧
      (∀ x, sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard x ∈
        poolFinset n \ priorBridgeReservation ∅ (Finset.range 5) batches) ∧
    ∃ (rows cols : List (LayerPacking.Layer n))
      (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
      (b : Cell n ≃ Fin (n * n)),
      rows.map Prod.fst = bridgeRepeatedPermutations 5 p ∧
      cols.map Prod.fst = bridgeRepeatedPermutations 5 p ∧
      LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols ∧
      (∀ t side, entry b (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
        fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeDiagonalSlot n (t, side))) ∧
      (∀ x, entry b (fwBridgeLayerCells rows cols hr hc x) =
        fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x)) ∧
      (∀ x : Fin (16 * (4 * 6)) × Fin 4,
        entry b (packedRectangleCorner hs choice (fwSeedRectangle hseedrect x.1, x.2)) =
          sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
            (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (prefixRectangleInput hdiag x))) ∧
      (∀ (j : Fin 16) (u : Fin (4 * 6)) (pair : Fin 2),
        entry b (packedRectangleCorner hs choice
            (fwSeedRectangle hseedrect (finProdFinEquiv (j, u)), prefixPairCorner pair true)) =
          entry b (packedRectangleCorner hs choice
            (fwSeedRectangle hseedrect (finProdFinEquiv (j, u)), prefixPairCorner pair false)) + 2) ∧
    ∃ (seedRows seedCols : List (LayerPacking.Layer n))
      (hsr : seedRows.length = 16 * 3) (hsc : seedCols.length = 16 * 3)
      (final : Cell n ≃ Fin (n * n)),
      seedRows.map Prod.fst = bridgeRepeatedPermutations 16 p ∧
      seedCols.map Prod.fst = bridgeRepeatedPermutations 16 p ∧
      LayerPacking.PackedLayers
        ((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
          LayerPacking.transposeCells (LayerPacking.layersSupport cols)) seedRows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        (((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
          LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪
          LayerPacking.layersSupport seedRows)) seedCols ∧
      Disjoint (LayerPacking.layersSupport seedRows)
        (LayerPacking.transposeCells (LayerPacking.layersSupport seedCols)) ∧
      (∀ (j : Fin 16) (k : Fin 3) (e : Fin n),
        (seedRows.get (bridgeStageLayerIndex hsr j k)).1 e = p k e ∧
        (seedCols.get (bridgeStageLayerIndex hsc j k)).1 e = p k e) ∧
      (∀ t side, entry final (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
        fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeDiagonalSlot n (t, side))) ∧
      (∀ x, entry final (fwBridgeLayerCells rows cols hr hc x) =
        fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x)) ∧
      (∀ x : Fin (16 * (4 * 6)) × Fin 4,
        entry final (packedRectangleCorner hs choice (fwSeedRectangle hseedrect x.1, x.2)) =
          sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
            (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (prefixRectangleInput hdiag x))) ∧
      (∀ x, entry final (fwSeedOrdinaryCells seedRows seedCols hsr hsc x) =
        sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
          (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x))) ∧
      (∀ (j : Fin 16) (u : Fin (4 * 6)) (pair : Fin 2),
        entry final (packedRectangleCorner hs choice
            (fwSeedRectangle hseedrect (finProdFinEquiv (j, u)), prefixPairCorner pair true)) =
          entry final (packedRectangleCorner hs choice
            (fwSeedRectangle hseedrect (finProdFinEquiv (j, u)), prefixPairCorner pair false)) + 2) ∧
      (∀ (i : Fin (16 * 3)) (e : Fin n),
        entry final (fwSeedOrdinaryCells seedRows seedCols hsr hsc (Sum.inl (i, (e, true)))) =
          entry final (fwSeedOrdinaryCells seedRows seedCols hsr hsc (Sum.inl (i, (e, false)))) + 2 ∧
        entry final (fwSeedOrdinaryCells seedRows seedCols hsr hsc (Sum.inr (i, (e, true)))) =
          entry final (fwSeedOrdinaryCells seedRows seedCols hsr hsc (Sum.inr (i, (e, false)))) + 2) ∧
    let retained := retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub
    let m : ℝ := (Lucas.poolTotal n : ℝ) / (n * n : ℕ)
    let low := bmorLowBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    let high := bmorHighBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    ∃ (cells : Fin (3 * (n / 450) * (3 * (n + 8))) × Fin 4 → Cell n),
      Function.Injective cells ∧
      (∀ x, cells x ∉ protectedPoolCells final
        (priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained)) ∧
    ∃ (blocks : List DoublePair)
      (hlen : blocks.length = 3 * (n / 450) * (3 * (n + 8))) (wide : Cell n ≃ Fin (n * n)),
      (∀ block ∈ blocks, block.MatchedValid low high) ∧
      blocks.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ block ∈ blocks, Disjoint block.footprint
        (priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained)) ∧
      (∀ x : Fin blocks.length × Fin 4,
        entry wide (cells (Fin.cast hlen x.1, x.2)) = doublePairSequenceEndpoint blocks x) ∧
      (∀ cell ∈ protectedPoolCells final
        (priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained), entry wide cell = entry final cell) ∧
      fwInstalledPairBounds m (poolMaximum n) blocks wide (fun x => cells (Fin.cast hlen x.1, x.2)) ∧
      (∀ i : Fin blocks.length, ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
        entry wide (cells (Fin.cast hlen i, 1)) = entry wide (cells (Fin.cast hlen i, 0)) + gap ∧
        entry wide (cells (Fin.cast hlen i, 2)) = entry wide (cells (Fin.cast hlen i, 3)) + gap ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n) ∧
      (∀ t side, entry wide (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
        entry final (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side))) ∧
      (∀ x, entry wide (fwBridgeLayerCells rows cols hr hc x) =
        entry final (fwBridgeLayerCells rows cols hr hc x)) ∧
      (∀ x : Fin (16 * (4 * 6)) × Fin 4,
        entry wide (packedRectangleCorner hs choice (fwSeedRectangle hseedrect x.1, x.2)) =
          entry final (packedRectangleCorner hs choice (fwSeedRectangle hseedrect x.1, x.2))) ∧
      (∀ x, entry wide (fwSeedOrdinaryCells seedRows seedCols hsr hsc x) =
        entry final (fwSeedOrdinaryCells seedRows seedCols hsr hsc x))
 := by
  dsimp only
  let choice := fwBridgeSeedRectangleChoice hrect hseedrect otherChoice
  obtain ⟨p, hder, hexp, batches, hvalid, hdisjoint, hbudget, candidates, hcard, hcand,
    kept, hsub, hkept, hvariance, hinj, hav, rows, cols, hr, hc, b, hrmap, hcmap,
    hrpacked, hcpacked, hbridgeDiag0, hbridgeOrd0, hseedDiag0, hseedGap0,
    seedRows, seedCols, hsr, hsc, final, hsrmap, hscmap, hsrpacked, hscpacked,
    hsdisjoint, hends, hbridgeDiag, hbridgeOrd, hseedDiag, hseedOrd, hseedGap, hseedOrdGap⟩ :=
    bmor_fw_bridge_and_seed_full_placement bmor upper lower n L hnlo hnhi hrect hseedrect hs
      otherChoice a seeds hseed hprime hcount
  let retained := retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub
  let removed := priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained
  have hretained : retained.card = 2 * (6 * (n + 8)) * 16 := by
    dsimp [retained, retainedSeedEndpoints]
    rw [Finset.card_image_of_injective _ hinj, retainedSeedLabels_card, hkept]
  have hlenBridge : ∀ j < 5, (batches j).length = 3 * (n + 8) := by
    intro j hj
    exact (hvalid j hj).1.1
  have hseedMem (x : (Fin 16 × Fin (6 * (n + 8))) × Bool) :
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept x) ∈ retained := by
    change _ ∈ retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub
    rw [← retainedSeedSlot_image candidates 17 16 (6 * (n + 8)) 2 hcard kept hsub hkept hinj]
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  obtain ⟨cells, hcells, hnew, blocks, hlen, wide, hmatched, hpair, havoid,
    hplaced, hfixed, hbounds, hgap, hpreserve⟩ :=
    fw_reflected_supply_with_protected_early_values bmor upper lower sharp hnlo hnhi
      ((Lucas.poolTotal n : ℝ) / (n * n : ℕ)) hmlo hmhi batches hlenBridge retained hretained final
  have hBD : ∀ t side, entry wide (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      entry final (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) := by
    intro t side
    apply hfixed
    apply (mem_protectedPoolCells final removed _).mpr
    rw [hbridgeDiag t side]
    exact Finset.mem_union_left _ (fwBridgeStageEndpoint_mem_final_reservation n batches hvalid _)
  have hBO : ∀ x, entry wide (fwBridgeLayerCells rows cols hr hc x) =
      entry final (fwBridgeLayerCells rows cols hr hc x) := by
    intro x
    apply hfixed
    apply (mem_protectedPoolCells final removed _).mpr
    rw [hbridgeOrd x]
    exact Finset.mem_union_left _ (fwBridgeStageEndpoint_mem_final_reservation n batches hvalid _)
  have hSD : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      entry wide (packedRectangleCorner hs choice (fwSeedRectangle hseedrect x.1, x.2)) =
        entry final (packedRectangleCorner hs choice (fwSeedRectangle hseedrect x.1, x.2)) := by
    intro x
    apply hfixed
    apply (mem_protectedPoolCells final removed _).mpr
    rw [hseedDiag x]
    exact Finset.mem_union_right _ (hseedMem _)
  have hSO : ∀ x, entry wide (fwSeedOrdinaryCells seedRows seedCols hsr hsc x) =
      entry final (fwSeedOrdinaryCells seedRows seedCols hsr hsc x) := by
    intro x
    apply hfixed
    apply (mem_protectedPoolCells final removed _).mpr
    rw [hseedOrd x]
    exact Finset.mem_union_right _ (hseedMem _)
  exact ⟨p, hder, hexp, batches, hvalid, hdisjoint, hbudget, candidates, hcard, hcand,
    kept, hsub, hkept, hvariance, hinj, hav, rows, cols, hr, hc, b, hrmap, hcmap,
    hrpacked, hcpacked, hbridgeDiag0, hbridgeOrd0, hseedDiag0, hseedGap0,
    seedRows, seedCols, hsr, hsc, final, hsrmap, hscmap, hsrpacked, hscpacked,
    hsdisjoint, hends, hbridgeDiag, hbridgeOrd, hseedDiag, hseedOrd, hseedGap, hseedOrdGap,
    cells, hcells, hnew, blocks, hlen, wide, hmatched, hpair, havoid, hplaced, hfixed,
    hbounds, hgap, hBD, hBO, hSD, hSO⟩

end
end Sude
