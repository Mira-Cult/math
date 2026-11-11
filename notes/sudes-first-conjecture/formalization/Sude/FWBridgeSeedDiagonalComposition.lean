import Sude.FWBridgeCommonSeed
import Sude.FWSeedOffsetPlacement

/-! Select and install FW bridge endpoints and retained seed rectangles in
one common RP1 packing. Ordinary seed placement remains separate. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- Every indexed bridge endpoint belongs to the actual final five-stage
reservation. -/
theorem fwBridgeStageEndpoint_mem_final_reservation
    (n : ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (x : (Fin 5 × Fin (3 * (n + 8))) × Fin 4) :
    fwBridgeStageEndpoint n ∅ batches hvalid x ∈
      priorBridgeReservation ∅ (Finset.range 5) batches := by
  rcases x with ⟨⟨j, i⟩, side⟩
  apply priorBridgeReservation_contains_batch ∅ (Finset.range 5) batches j
    (Finset.mem_range.mpr j.isLt)
  apply doublePair_footprint_subset_batch (batches j) _
    (fwBridgeStageBlock_mem n ∅ batches hvalid j i)
  exact DoublePair.endpoint_mem _ side

/-- With the quota explicitly supplied, select five valid bridge batches and
one retained seed family, install the bridge rectangles and ordinary layers,
then install those very seed endpoints in offset rectangles. All bridge
endpoint cells stay fixed; the ordinary seed network and later controller
compatibility are not asserted. -/
theorem bmor_fw_bridge_and_seed_diagonal_placement
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (n L : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
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
            (fwSeedRectangle hseedrect (finProdFinEquiv (j, u)), prefixPairCorner pair false)) + 2) := by
  dsimp only
  let seedChoice := fwSeedRectangleChoice hseedrect otherChoice
  let choice := fwBridgeSeedRectangleChoice hrect hseedrect otherChoice
  obtain ⟨p, hderange, hexp⟩ := fw_permutation_expander_exists hnlo
  have hlen : (bridgeRepeatedPermutations 5 p).length = 15 := by
    simpa using (bridgeRepeatedPermutations_length (J := 5) p)
  have hder : ∀ π ∈ bridgeRepeatedPermutations 5 p, ∀ i, π i ≠ i :=
    bridgeRepeatedPermutations_derange p hderange
  obtain ⟨batches, hvalid, hdisjoint, hbudget, rows, cols, hr, hc, a', hrmap, hcmap,
    hrpacked, hcpacked, hinjcells, hfree, hdiag, hord, hdiagGap, hordGap⟩ :=
    bmor_fw_five_bridge_packed_placement bmor upper lower n L hnlo hnhi
      hrect hs seedChoice a (bridgeRepeatedPermutations 5 p)
      (bridgeRepeatedPermutations 5 p) hlen hlen hder hder
  have hbridge := fw_selected_bridge_values_pool_and_quarter bmor upper n batches
    (by omega) (by omega) hvalid
  obtain ⟨candidates, hcard, hcand, kept, hsub, hkept, hvariance, hinj, hav⟩ :=
    fw_actual_narrow_seed_of_quota lower n seeds (priorBridgeReservation ∅ (Finset.range 5) batches)
      hnlo hnhi hseed hprime (fun q hq => (hbridge q hq).2) hcount
  let diagCells : Finset (Cell n) := allocatedBridgeRectangleSupport hrect hs choice
  let ordinaryCells : Finset (Cell n) := Finset.univ.image (fwBridgeLayerCells rows cols hr hc)
  let base := diagCells ∪ ordinaryCells
  have hbase : ∀ c ∈ base, entry a' c ∈ priorBridgeReservation ∅ (Finset.range 5) batches := by
    intro c hc'
    rcases Finset.mem_union.mp hc' with hc' | hc'
    · obtain ⟨⟨t, side⟩, _, rfl⟩ := Finset.mem_image.mp hc'
      change entry a' (packedRectangleCorner hs (bridgeDiagonalChoice hrect seedChoice) (bridgeDiagonalRectangle hrect t, side)) ∈ _
      rw [hdiag t side]
      exact fwBridgeStageEndpoint_mem_final_reservation n batches hvalid _
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc'
      rw [hord x]
      exact fwBridgeStageEndpoint_mem_final_reservation n batches hvalid _
  have hseedfree : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      packedRectangleCorner hs choice (fwSeedRectangle hseedrect x.1, x.2) ∉ base := by
    rintro ⟨t, side⟩ hmem
    rcases Finset.mem_union.mp hmem with hmem | hmem
    · obtain ⟨⟨b, bs⟩, _, heq⟩ := Finset.mem_image.mp hmem
      have heq' := packedRectangleCorner_injective hs choice heq
      exact fw_bridge_seed_rectangle_ne hrect hseedrect b t (congrArg Prod.fst heq')
    · obtain ⟨x, _, heq⟩ := Finset.mem_image.mp hmem
      apply hfree x
      rw [heq]
      exact Finset.mem_image.mpr ⟨(fwSeedRectangle hseedrect t, side), Finset.mem_univ _, rfl⟩
  obtain ⟨b, hseedPlaced, hfixed, hseedGap⟩ :=
    fw_install_retained_seed_offset_rectangles n L candidates hcard kept hsub hkept
      (priorBridgeReservation ∅ (Finset.range 5) batches) hav hinj hrect hseedrect hs otherChoice a' base hbase hseedfree
  have hdiag' : ∀ t side, entry b (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeDiagonalSlot n (t, side)) := by
    intro t side
    rw [hfixed _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(t, side), Finset.mem_univ _, rfl⟩))]
    exact hdiag t side
  have hord' : ∀ x, entry b (fwBridgeLayerCells rows cols hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x) := by
    intro x
    rw [hfixed _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩))]
    exact hord x
  exact ⟨p, hderange, hexp, batches, hvalid, hdisjoint, hbudget,
    candidates, hcard, hcand, kept, hsub, hkept, hvariance, hinj, hav,
    rows, cols, hr, hc, b, hrmap, hcmap, hrpacked, hcpacked, hdiag', hord', hseedPlaced, hseedGap⟩

end
end Sude
