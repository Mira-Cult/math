import Sude.FWCrossingJointPhysicalOfTheta
import Sude.FWJointCrossingSwitches

/-! Preserve the same crossing and wide-grid witness and switch arbitrary network subsets. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- The same crossing witness carries its wide-stage grids and permits
simultaneous switches of arbitrary subsets of the jointly packed networks.
This does not choose flows or establish line-sum corrections. -/
theorem bmor_fw_enhanced_crossing_joint_switches_of_theta
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    (n : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hcount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card) :
    let hrect := (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).1
    let hseedrect := (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).2.1
    let hwide := (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).2.2.1
    let hs := (fw_reserved_wide_rectangle_capacity hnlo (by decide) (by decide)).2.2.2
    let hmax := fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)
    let choice := fwBridgeSeedRectangleChoice hrect hseedrect
      (fwWideRectangleChoice hwide (fwGrowthRectangleChoice hmax otherChoice))
    ∃ p : Fin 3 → Equiv.Perm (Fin n),
      (∀ i v, p i v ≠ v) ∧
      (∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
        500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card) ∧
    ∃ (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j),
    ∃ (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
      (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16),
      candidates ⊆ seeds ∧
      (let w := sortedSeedReal candidates 17 (6 * (n + 8)) hcard
       ∃ z : ℝ, (∃ i ∈ kept, z = w (i * (6 * (n + 8)) + (6 * (n + 8) - 1)) - w (i * (6 * (n + 8)))) ∧
        (∀ i ∈ kept, w (i * (6 * (n + 8)) + (6 * (n + 8) - 1)) - w (i * (6 * (n + 8))) ≤ z) ∧
        3 * 6 * (∑ i ∈ kept, (w (i * (6 * (n + 8)) + (6 * (n + 8) - 1)) - w (i * (6 * (n + 8)))) ^ 2) + 4 * z ^ 2 ≤
          (11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2) ∧
      Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard) ∧
      (∀ x, sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard x ∈
        poolFinset n \ priorBridgeReservation ∅ (Finset.range 5) batches) ∧
    ∃ (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
      (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
      (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
      (hwc : wc.length = (3 * (n / 450)) * 3)
      (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
      (old : Cell n ≃ Fin (n*n)) (stock : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
    let initial := ((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
    let offset := 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)
    let hpool : ∀ v ∈ initial, v ∈ pool n := by
      intro v hv
      exact mem_poolFinset.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
    let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
    let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
    ∃ (trace : BTGrowingTrace 2 (6 * (n + 8)) initial 32 stock last stages)
      (hoff : offset + stages.length * (4 * 6) ≤ fwJointRectangleCount n 254)
      (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3)
      (hgc : gc.length = stages.length * 3) (grown : Cell n ≃ Fin (n*n)),
      stages.length ≤ 238 ∧
      stock ⊆ initial ∧
      stock.card + 2 * (6 * (n + 8)) * stages.length = initial.card ∧
      ((6 * (n + 8) : ℕ) : ℝ) ≤ (1 / 69780 : ℝ) * (poolMaximum n : ℝ) ∧
      fwVaryingStockMass (poolMaximum n) stages.length ≤ (stock.card : ℝ) ∧
      (poolMaximum n : ℝ) / 23 ≤ last ∧
      stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ stage ∈ stages, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) stages ∧
      (∀ c ∈ fwGrowthEarlyRoleCells hrect hseedrect hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc,
        entry grown c = entry old c) ∧
      rows.map Prod.fst = bridgeRepeatedPermutations 5 p ∧
      cols.map Prod.fst = bridgeRepeatedPermutations 5 p ∧
      sr.map Prod.fst = bridgeRepeatedPermutations 16 p ∧
      sc.map Prod.fst = bridgeRepeatedPermutations 16 p ∧
      gr.map Prod.fst = bridgeRepeatedPermutations stages.length p ∧
      gc.map Prod.fst = bridgeRepeatedPermutations stages.length p ∧
      (∀ (j : Fin stages.length) (i : Fin (4 * 6)),
        choice (btGrowingOffsetRectangle offset hoff (finProdFinEquiv (j, i))) = decide (i.val < 2 * 6)) ∧
      LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows) (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      LayerPacking.PackedLayers
        ((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
          LayerPacking.transposeCells (LayerPacking.layersSupport cols)) sr ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        (((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
          LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪ LayerPacking.layersSupport sr)) sc ∧
      Disjoint (LayerPacking.layersSupport sr) (LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∧
      (let base := (((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪ LayerPacking.layersSupport sr) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport sc)
       LayerPacking.PackedLayers base wr ∧
       LayerPacking.PackedLayers (LayerPacking.transposeCells (base ∪ LayerPacking.layersSupport wr)) wc ∧
       Disjoint (LayerPacking.layersSupport wr) (LayerPacking.transposeCells (LayerPacking.layersSupport wc))) ∧
      LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((rows ++ sr) ++ wr) ++ gr) ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((rows ++ sr) ++ wr) ++ gr)))
          (((cols ++ sc) ++ wc) ++ gc) ∧
      LayerPacking.PackedLayers (fwGrowthEarlyBase hs choice rows cols sr sc wr wc) gr ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        (fwGrowthEarlyBase hs choice rows cols sr sc wr wc ∪ LayerPacking.layersSupport gr)) gc ∧
      Disjoint (LayerPacking.layersSupport gr) (LayerPacking.transposeCells (LayerPacking.layersSupport gc)) ∧
      (∀ x : PrefixPhysicalInputs stages.length 6 3 n,
        entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
          (trace.poolValues rfl hpool (prefixPhysicalInput hfit hdiag x)).val) ∧
      (∀ (j : Fin stages.length) (u : Fin (4 * 6)) (pair : Fin 2),
        entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc
          (Sum.inl (finProdFinEquiv (j, u), prefixPairCorner pair true))) =
        entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc
          (Sum.inl (finProdFinEquiv (j, u), prefixPairCorner pair false))) +
            (BTStageTrace.stageAt stages rfl j).gap) ∧
      (∀ y : (Fin stages.length × Fin (6 * (n + 8))) × Bool,
        ∃ x : PrefixPhysicalInputs stages.length 6 3 n,
          prefixPhysicalInput hfit hdiag x = y ∧
          entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
            (trace.poolValues rfl hpool y).val) ∧
      (∀ t side, entry old (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
        fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeDiagonalSlot n (t, side))) ∧
      (∀ x : Fin (16 * (4 * 6)) × Fin 4,
        entry old (packedRectangleCorner hs choice (fwSeedRectangle hseedrect x.1, x.2)) =
          sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
            (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (prefixRectangleInput hdiag x))) ∧
      (∀ x, entry old (fwSeedOrdinaryCells sr sc hsr hsc x) =
        sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
          (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x))) ∧
      (∀ x, entry old (fwBridgeLayerCells rows cols hr hc x) =
        fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x)) ∧
      (∀ (i : Fin (stages.length * 3)) (e : Fin n),
        entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, true))))) =
        entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, false))))) +
          variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e) ∧
      (∀ (i : Fin (stages.length * 3)) (e : Fin n),
        entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, true))))) =
        entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, false))))) +
          variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e) ∧
      (let m : ℝ := (Lucas.poolTotal n : ℝ) / (n * n : ℕ)
       let low := bmorLowBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
       let high := bmorHighBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
       ∀ block ∈ blocks, block.MatchedValid low high) ∧
      blocks.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ block ∈ blocks, Disjoint block.footprint
        (fwBridgeSeedProtectedValues batches candidates hcard kept hsub)) ∧
      (∀ x : FWWideInputs n,
        entry old (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
          doublePairSequenceEndpoint blocks
            (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2)) ∧
      (∀ (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n),
        ∃ wideGap : ℕ, 0 < wideGap ∧ wideGap % 2 = 0 ∧
          (∀ network : Bool,
            entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e network true)) =
            entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e network false)) + wideGap) ∧
          (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (wideGap : ℝ) ∧ (wideGap : ℝ) < poolMaximum n) ∧
      (∀ (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) (side : Bool),
        fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e false side) =
          ((if side then p k e else e), (wr.get (bridgeStageLayerIndex hwr j k)).2 e) ∧
        fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e true side) =
          ((wc.get (bridgeStageLayerIndex hwc j k)).2 e, (if side then p k e else e))) ∧
      (∀ (edge : Fin 3 × Fin n) (network : Bool),
        let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
        let radius := last + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j
        let initialGap := fwPhysicalEdgeTraceGap grown (fwSeedEdgeCells sr sc hsr hsc edge network)
          (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network)
        CompleteEvenGrid
          ((Finset.univ : Finset (Sum (Fin 16) (Fin stages.length))).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
            (Finset.range 5).image (Sum.inr : ℕ → Sum (Sum (Fin 16) (Fin stages.length)) ℕ))
          (joinedBridgeGap initialGap batches index) radius ∧
        (poolMaximum n : ℝ) ≤ radius ∧
        (∀ j : Fin 5, entry grown (fwBridgeLayerCells rows cols hr hc ((j, edge), (network, true))) =
          entry grown (fwBridgeLayerCells rows cols hr hc ((j, edge), (network, false))) +
            selectedBridgeGap batches index j)) ∧
      (∀ (edge : Fin 3 × Fin n) (network : Bool),
        let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
        let radius := last + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j
        let initialGap := fwPhysicalEdgeTraceGap grown (fwSeedEdgeCells sr sc hsr hsc edge network)
          (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network)
        let base : Finset (Sum (Sum (Fin 16) (Fin stages.length)) ℕ) :=
          ((Finset.univ : Finset (Sum (Fin 16) (Fin stages.length))).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
            (Finset.range 5).image (Sum.inr : ℕ → Sum (Sum (Fin 16) (Fin stages.length)) ℕ))
        ∃ wide : Fin (3 * (n / 450)) → ℕ,
          (∀ j, 0 < wide j ∧ 2 ∣ wide j ∧
            (∀ sideNetwork : Bool,
              entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 sideNetwork true)) =
              entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 sideNetwork false)) + wide j) ∧
            (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (wide j : ℝ) ∧ (wide j : ℝ) < poolMaximum n) ∧
          CompleteEvenGrid
            (base.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩)
            (Sum.elim (joinedBridgeGap initialGap batches index) wide) (radius + ∑ j, wide j) ∧
          2 ∣ radius + ∑ j, wide j ∧
          (2 : ℝ) * (n / 450 : ℕ) * (poolMaximum n : ℝ) ≤ ∑ j, (wide j : ℝ)) ∧
      (∀ (Sr : Finset (Fin (((rows ++ sr) ++ wr) ++ gr).length × Fin n))
         (Sc : Finset (Fin (((cols ++ sc) ++ wc) ++ gc).length × Fin n)),
        let rowLayers := ((rows ++ sr) ++ wr) ++ gr
        let colLayers := ((cols ++ sc) ++ wc) ++ gc
        let rowGap := fwPhysicalRowLayerGap grown rowLayers
        let colGap := fwPhysicalColumnLayerGap grown colLayers
        ∃ b : Cell n ≃ Fin (n*n),
          (∀ r, (rowSum b r : ℤ) - (rowSum grown r : ℤ) =
            ∑ k ∈ Sr, layerTransfer rowLayers rowGap k r) ∧
          (∀ c, (columnSum b c : ℤ) - (columnSum grown c : ℤ) =
            ∑ k ∈ Sc, layerTransfer colLayers colGap k c) ∧
          mainSum b = mainSum grown ∧ antiSum b = antiSum grown ∧
          (∀ c ∈ packedRectangleSupport hs choice, entry b c = entry grown c) ∧
          Set.range (entry b) = pool n ∧ Function.Injective (entry b)) := by
  dsimp only
  obtain ⟨p, hder, hexp, batches, hvalid, candidates, hcard, kept, hsub, hkept,
    hcand, hvariance, hinj, hav, rows, cols, hr, hc, sr, sc, hsr, hsc,
    wr, wc, hwr, hwc, blocks, hlen, old, stock, last, stages, trace, hoff,
    gr, gc, hgr, hgc, grown, hcap, hstocksub, hstockcard, hq, hmass,
    hcross, hpairwise, havoidTrace, hnarrow, hfixed,
    hrmap, hcmap, hsrmap, hscmap, hgrmap, hgcmap, hchoice,
    hrows, hcols, hbrdisj, hsrows, hscols, hsdisj, hwpack, hjointrow, hjointcol,
    hgrpacked, hgcpacked, hgdisj, hplaced, hdiagGap, hcomplete,
    hbd, hsd, hso, hbo, hrow, hcol, hmatched, hpair, havoid, hwp,
    hwidegap, hwidecoords, hbridgegrid, hwidegrid⟩ :=
    bmor_fw_enhanced_crossing_joint_physical_of_theta mv bmor upper lower sharp upperSharp
      n hnlo hnhi otherChoice a seeds hseed hprime hcount
  refine ⟨p, hder, hexp, batches, hvalid, candidates, hcard, kept, hsub, hkept,
    hcand, hvariance, hinj, hav, rows, cols, hr, hc, sr, sc, hsr, hsc,
    wr, wc, hwr, hwc, blocks, hlen, old, stock, last, stages, trace, hoff,
    gr, gc, hgr, hgc, grown, hcap, hstocksub, hstockcard, hq, hmass,
    hcross, hpairwise, havoidTrace, hnarrow, hfixed,
    hrmap, hcmap, hsrmap, hscmap, hgrmap, hgcmap, hchoice,
    hrows, hcols, hbrdisj, hsrows, hscols, hsdisj, hwpack, hjointrow, hjointcol,
    hgrpacked, hgcpacked, hgdisj, hplaced, hdiagGap, hcomplete,
    hbd, hsd, hso, hbo, hrow, hcol, hmatched, hpair, havoid, hwp,
    hwidegap, hwidecoords, hbridgegrid, hwidegrid, ?_⟩
  intro Sr Sc
  exact fw_joint_crossing_toggle_networks batches hvalid candidates hcard kept hsub hkept hav
    _ _ _ _ _ rows cols hr hc sr sc hsr hsc wr wc hwr hwc old grown hfixed hbo hso
    hwidegap _ hoff gr gc hgr hgc hrow hcol hrows hcols hsrows hscols hwpack.1 hwpack.2.1
    (by simpa [fwGrowthEarlyBase] using hgrpacked)
    (by simpa [fwGrowthEarlyBase] using hgcpacked) Sr Sc

end
end Sude
