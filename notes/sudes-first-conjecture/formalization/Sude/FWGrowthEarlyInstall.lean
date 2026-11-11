import Sude.FWGrowthEarlyValues
import Sude.FWGrowthLayerPacking
import Sude.BTGrowingOffsetPhysical

/-! Install a supplied FW growth trace after the same actual early role
witnesses. No trace existence, crossing, or unprotected-cell preservation is
asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Given the actual early square and a supplied screened growth trace,
construct growth layers for a supplied derangement triple and install that trace's endpoints
in offset rectangles and ordinary networks, preserving every earlier role.
The caller supplies `choice`; no main/anti diagonal allocation is asserted. -/
theorem fw_install_growth_after_actual_early {n L P : ℕ}
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hP : P ≤ 238)
    (p : Fin 3 → Equiv.Perm (Fin n)) (hder : ∀ k e, p k e ≠ e)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hlenBlocks : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hsrows : LayerPacking.PackedLayers
      ((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) sr)
    (hscols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪ LayerPacking.layersSupport sr)) sc)
    (hsdisj : Disjoint (LayerPacking.layersSupport sr) (LayerPacking.transposeCells (LayerPacking.layersSupport sc)))
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    (hwrows : LayerPacking.PackedLayers
      ((((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪ LayerPacking.layersSupport sr) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport sc)) wr)
    (hwcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪ LayerPacking.layersSupport sr) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∪ LayerPacking.layersSupport wr)) wc)
    (a : Cell n ≃ Fin (n*n))
    (hbd : ∀ t side, entry a (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (hbo : ∀ x, entry a (fwBridgeLayerCells rows cols hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    (hsd : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      entry a (packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) =
        sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
          (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (prefixRectangleInput (by omega) x)))
    (hso : ∀ x, entry a (fwSeedOrdinaryCells sr sc hsr hsc x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x)))
    (hwp : ∀ x : FWWideInputs n, entry a (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlenBlocks.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    {stock : Finset ℕ} {last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) 32 stock last stages)
    (hlen : stages.length = P) :
    let offset := 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)
    let initial := ((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
    let hpool : ∀ v ∈ initial, v ∈ pool n := by
      intro v hv
      exact mem_poolFinset.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
    let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
    let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
    ∃ (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
      (b : Cell n ≃ Fin (n*n)),
      gr.map Prod.fst = bridgeRepeatedPermutations P p ∧
      gc.map Prod.fst = bridgeRepeatedPermutations P p ∧
      LayerPacking.PackedLayers (fwGrowthEarlyBase hs choice rows cols sr sc wr wc) gr ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        (fwGrowthEarlyBase hs choice rows cols sr sc wr wc ∪ LayerPacking.layersSupport gr)) gc ∧
      Disjoint (LayerPacking.layersSupport gr) (LayerPacking.transposeCells (LayerPacking.layersSupport gc)) ∧
      (∀ (j : Fin P) (k : Fin 3) (e : Fin n),
        (gr.get (bridgeStageLayerIndex hgr j k)).1 e = p k e ∧
        (gc.get (bridgeStageLayerIndex hgc j k)).1 e = p k e) ∧
      (∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc,
        entry b c = entry a c) ∧
      (∀ x : PrefixPhysicalInputs P 6 3 n,
        entry b (btGrowingOffsetCells offset hgrowth hs choice gr gc hgr hgc x) =
          (trace.poolValues hlen hpool (prefixPhysicalInput hfit hdiag x)).val) ∧
      (∀ (j : Fin P) (u : Fin (4 * 6)) (pair : Fin 2),
        entry b (btGrowingOffsetCells offset hgrowth hs choice gr gc hgr hgc
          (Sum.inl (finProdFinEquiv (j, u), prefixPairCorner pair true))) =
        entry b (btGrowingOffsetCells offset hgrowth hs choice gr gc hgr hgc
          (Sum.inl (finProdFinEquiv (j, u), prefixPairCorner pair false))) +
            (BTStageTrace.stageAt stages hlen j).gap) ∧
      (∀ (i : Fin (P * 3)) (e : Fin n),
        entry b (btGrowingOffsetCells offset hgrowth hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, true))))) =
        entry b (btGrowingOffsetCells offset hgrowth hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, false))))) +
          variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages hlen j).gap) rfl i e) ∧
      (∀ (i : Fin (P * 3)) (e : Fin n),
        entry b (btGrowingOffsetCells offset hgrowth hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, true))))) =
        entry b (btGrowingOffsetCells offset hgrowth hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, false))))) +
          variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages hlen j).gap) rfl i e) ∧
      (∀ y : (Fin P × Fin (6 * (n + 8))) × Bool, ∃ x : PrefixPhysicalInputs P 6 3 n,
        prefixPhysicalInput hfit hdiag x = y ∧
        entry b (btGrowingOffsetCells offset hgrowth hs choice gr gc hgr hgc x) =
          (trace.poolValues hlen hpool y).val) := by
  dsimp only
  let offset := 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)
  let initial := ((poolFinset n).filter (fun p => 43 < p)) \
    fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
  let base := fwGrowthEarlyBase hs choice rows cols sr sc wr wc
  let prior := fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc
  have hpool : ∀ v ∈ initial, v ∈ pool n := by
    intro v hv
    exact mem_poolFinset.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
  have havoids : ∀ v ∈ initial, v ∉ fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks := by
    intro v hv
    exact (Finset.mem_sdiff.mp hv).2
  have hprior : prior ⊆ base := fw_growth_early_roles_subset_base hrect hseed hwide hs choice
    rows cols hr hc sr sc hsr hsc wr wc hwr hwc
  have hpriorValues : ∀ c ∈ prior, entry a c ∈ fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks :=
    fw_growth_early_role_values batches hvalid candidates hcard kept hsub hkept hinj blocks hlenBlocks
      hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc a hbd hbo hsd hso hwp
  have hrectbase : packedRectangleSupport hs choice ⊆ base := by
    intro c hc'
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hc')))))
  have hdiagfree : ∀ x : Fin (P * (4 * 6)) × Fin 4,
      packedRectangleCorner hs choice (btGrowingOffsetRectangle offset hgrowth x.1, x.2) ∉ prior := by
    intro x
    exact fw_growth_corner_avoids_early_roles hrect hseed hwide hgrowth hs choice
      rows cols hr hc hrows hcols sr sc hsr hsc hsrows hscols hsdisj wr wc hwr hwc hwrows hwcols x
  obtain ⟨gr, gc, hgr, hgc, hgrmap, hgcmap, hgrpacked, hgcpacked, hgdisj, hends⟩ :=
    fw_pack_growth_layers_after_wide hnlo hnhi hP hs choice p hder rows cols sr sc wr wc
      hr hc hsr hsc hwr hwc hrows hcols hsrows hscols hwrows hwcols
  obtain ⟨b, hplaced, hfixed, hdiagGap, hrowGap, hcolGap, hcomplete⟩ :=
    trace.install_offset_roles hlen (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) offset hgrowth hs choice hpool
      (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) havoids a base prior
      hrectbase hprior hpriorValues hdiagfree gr gc hgr hgc hgrpacked hgcpacked hgdisj
  exact ⟨gr, gc, hgr, hgc, b, hgrmap, hgcmap, hgrpacked, hgcpacked, hgdisj, hends, hfixed,
    hplaced, hdiagGap, hrowGap, hcolGap, hcomplete (by omega)⟩

end
end Sude
