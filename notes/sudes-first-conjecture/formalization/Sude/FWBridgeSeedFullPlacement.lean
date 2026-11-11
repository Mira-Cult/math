import Sude.FWSeedOrdinaryPlacement

/-! Joint actual placement of FW bridges and retained seed endpoints.
Growing stages, wide blocks and the complete controller remain separate. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- Select the actual FW bridge batches and quota-based retained seed groups,
then place both populations in one square using the same expander and joint
RP1 geometry. Seed quota and the cited analytic inputs remain assumptions. -/
theorem bmor_fw_bridge_and_seed_full_placement
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
          entry final (fwSeedOrdinaryCells seedRows seedCols hsr hsc (Sum.inr (i, (e, false)))) + 2)
 := by
  dsimp only
  let choice := fwBridgeSeedRectangleChoice hrect hseedrect otherChoice
  obtain ⟨p, hder, hexp, batches, hvalid, hdisjoint, hbudget,
    candidates, hcard, hcand, kept, hsub, hkept, hvariance, hinj, hav,
    rows, cols, hr, hc, b, hrmap, hcmap, hrpacked, hcpacked,
    hbridgeDiag, hbridgeOrd, hseedDiag, hseedGap⟩ :=
    bmor_fw_bridge_and_seed_diagonal_placement bmor upper lower n L hnlo hnhi
      hrect hseedrect hs otherChoice a seeds hseed hprime hcount
  let prior : Finset (Cell n) := allocatedBridgeRectangleSupport hrect hs choice ∪
    Finset.univ.image (fwBridgeLayerCells rows cols hr hc)
  let base : Finset (Cell n) := (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport cols)
  have hpriorSub : prior ⊆ base := by
    intro c hc'
    rcases Finset.mem_union.mp hc' with hc' | hc'
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (allocatedBridgeRectangleSupport_subset hrect hs choice hc'))
    · obtain ⟨⟨q, ⟨network, side⟩⟩, _, rfl⟩ := Finset.mem_image.mp hc'
      cases network
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact LayerPacking.layerSupport_subset _ rows (List.get_mem rows _) (LayerPacking.sequenceCell_mem rows _ _)
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        exact ⟨_, LayerPacking.layerSupport_subset _ cols (List.get_mem cols _)
          (LayerPacking.sequenceCell_mem cols _ _), rfl⟩
  have hrectSub : packedRectangleSupport hs choice ⊆ base := by
    intro c hc'
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hc')
  have hpriorValues : ∀ c ∈ prior, entry b c ∈ priorBridgeReservation ∅ (Finset.range 5) batches := by
    intro c hc'
    rcases Finset.mem_union.mp hc' with hc' | hc'
    · obtain ⟨⟨t, side⟩, _, rfl⟩ := Finset.mem_image.mp hc'
      change entry b (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) ∈ _
      rw [hbridgeDiag t side]
      exact fwBridgeStageEndpoint_mem_final_reservation n batches hvalid _
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc'
      rw [hbridgeOrd x]
      exact fwBridgeStageEndpoint_mem_final_reservation n batches hvalid _
  obtain ⟨seedRows, seedCols, hsr, hsc, hsrmap, hscmap, hsrpacked, hscpacked,
    hsdisjoint, hsrsafe, hscsafe, hends⟩ :=
    fw_pack_seed_layers_after_bridge hnlo hs choice p hder rows cols hr hc hrpacked hcpacked
  obtain ⟨final, hordSeed, hfixedPrior, hfixedSeed, hordGap⟩ :=
    fw_install_retained_seed_ordinary n L candidates hcard kept hsub hkept
      (priorBridgeReservation ∅ (Finset.range 5) batches) hav hinj hseedrect hs choice b prior base
      hpriorSub hrectSub hpriorValues hseedDiag seedRows seedCols hsr hsc hsrpacked hscpacked hsdisjoint
  have hbridgeDiag' : ∀ t side, entry final (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeDiagonalSlot n (t, side)) := by
    intro t side
    rw [hfixedPrior _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(t, side), Finset.mem_univ _, rfl⟩))]
    exact hbridgeDiag t side
  have hbridgeOrd' : ∀ x, entry final (fwBridgeLayerCells rows cols hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x) := by
    intro x
    rw [hfixedPrior _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩))]
    exact hbridgeOrd x
  have hseedDiag' : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      entry final (packedRectangleCorner hs choice (fwSeedRectangle hseedrect x.1, x.2)) =
        sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
          (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept
            (prefixRectangleInput (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) x)) := by
    intro x
    rw [hfixedSeed x]
    exact hseedDiag x
  have hseedGap' : ∀ (j : Fin 16) (u : Fin (4 * 6)) (pair : Fin 2),
      entry final (packedRectangleCorner hs choice
          (fwSeedRectangle hseedrect (finProdFinEquiv (j, u)), prefixPairCorner pair true)) =
        entry final (packedRectangleCorner hs choice
          (fwSeedRectangle hseedrect (finProdFinEquiv (j, u)), prefixPairCorner pair false)) + 2 := by
    intro j u pair
    rw [hfixedSeed (finProdFinEquiv (j, u), prefixPairCorner pair true),
      hfixedSeed (finProdFinEquiv (j, u), prefixPairCorner pair false)]
    exact hseedGap j u pair
  exact ⟨p, hder, hexp, batches, hvalid, hdisjoint, hbudget,
    candidates, hcard, hcand, kept, hsub, hkept, hvariance, hinj, hav,
    rows, cols, hr, hc, b, hrmap, hcmap, hrpacked, hcpacked,
    hbridgeDiag, hbridgeOrd, hseedDiag, hseedGap,
    seedRows, seedCols, hsr, hsc, final, hsrmap, hscmap, hsrpacked, hscpacked, hsdisjoint, hends,
    hbridgeDiag', hbridgeOrd', hseedDiag', hordSeed, hseedGap', hordGap⟩

end
end Sude
