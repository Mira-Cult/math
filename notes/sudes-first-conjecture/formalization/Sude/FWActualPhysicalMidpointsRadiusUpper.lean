import Sude.FWActualStrongWideGapTotalsRadiusUpper
import Sude.FWPhysicalMidpointInvoice
import Sude.FWInstalledNetworkGapTotal
import Sude.FWActualStrongWideInvoice
import Sude.FWJointCrossingGaps
import Sude.FWActualEdgeGridTransport
import Sude.FWJointSupportedCellSeparation

/-! Physical midpoint bounds and a radius upper bound for the same
theta-based crossing witness. No older selector is identified. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- Preserve all original same-square crossing and actual-grid outputs, and
realize arbitrary supplied bounded row and column graph flows from one common
reference, together with its actual-network centering invoice, physical gap totals, and
physical midpoint comparison. No line-mean bound, target-flow feasibility or
prime-line conclusion is asserted. -/
theorem bmor_fw_actual_grids_supplied_flows_with_physical_midpoints_of_theta_radius_upper
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    (n : ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
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
      0 ≤ (stock.card : ℝ) ∧
      (poolMaximum n : ℝ) / 23 ≤ last ∧
      (last : ℝ) ≤ max (32 : ℝ) (2 * ((poolMaximum n : ℝ) / 23)) ∧
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
          Set.range (entry b) = pool n ∧ Function.Injective (entry b)) ∧
      (let br := rows
          let bc := cols
          let P := stages.length
          let rect := packedRectangleSupport hs choice
       let α := ({t // t ∈ fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))} × Fin 3) × Fin n
       let rslot : α → Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n :=
         fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr
       let cslot : α → Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n :=
         fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc
       Function.Injective (fun x : α × Bool => layerPairSlot (((br ++ sr) ++ wr) ++ gr) (rslot x.1) x.2) ∧
       Function.Injective (fun x : α × Bool => (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (cslot x.1) x.2).swap) ∧
       (∀ x y : α × Bool, layerPairSlot (((br ++ sr) ++ wr) ++ gr) (rslot x.1) x.2 ≠
         (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (cslot y.1) y.2).swap) ∧
       (∀ x : α × Bool, layerPairSlot (((br ++ sr) ++ wr) ++ gr) (rslot x.1) x.2 ∉ rect) ∧
       (∀ x : α × Bool, (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (cslot x.1) x.2).swap ∉ rect)) ∧
         (∀ edge : Fin 3 × Fin n,
          let br := rows
          let bc := cols
       let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
       let radius := last + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j
       let labels := fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))
       let rows := ((br ++ sr) ++ wr) ++ gr
       let cols := ((bc ++ sc) ++ wc) ++ gc
       let rowSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)
       let colSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)
       ∃ wide : Fin (3 * (n / 450)) → ℕ,
         (∀ j, 0 < wide j ∧ 2 ∣ wide j ∧
           (∀ network : Bool,
             entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
             entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide j) ∧
           (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (wide j : ℝ) ∧ (wide j : ℝ) < poolMaximum n) ∧
         CompleteEvenGrid (labels.attach.image rowSlot) (fun x => fwPhysicalRowLayerGap grown rows x.1 x.2)
           (radius + ∑ j, wide j) ∧
         CompleteEvenGrid (labels.attach.image colSlot) (fun x => fwPhysicalColumnLayerGap grown cols x.1 x.2)
           (radius + ∑ j, wide j) ∧
         (∀ x side, LayerPacking.sequenceCell rows ((rowSlot x).1, ((rowSlot x).2, side)) =
           ((if side then p edge.1 edge.2 else edge.2), (rows.get (rowSlot x).1).2 edge.2)) ∧
         (∀ x side, (LayerPacking.sequenceCell cols ((colSlot x).1, ((colSlot x).2, side))).swap =
           ((cols.get (colSlot x).1).2 edge.2, (if side then p edge.1 edge.2 else edge.2))) ∧
         2 ∣ radius + ∑ j, wide j ∧
         (2 : ℝ) * (n / 450 : ℕ) * (poolMaximum n : ℝ) ≤ ∑ j, (wide j : ℝ)) ∧
      (let rect := packedRectangleSupport hs choice
    let N := (n / 450) * poolMaximum n
       let source : Fin 3 × Fin n → Fin n := fun e => e.2
       let target : Fin 3 × Fin n → Fin n := fun e => p e.1 e.2
    let rowLayers := ((rows ++ sr) ++ wr) ++ gr
    let colLayers := ((cols ++ sc) ++ wc) ++ gc
    let rowGap := fwPhysicalRowLayerGap grown rowLayers
    let colGap := fwPhysicalColumnLayerGap grown colLayers
    ∃ (hrowPack : LayerPacking.PackedLayers rect rowLayers)
      (hcolPack : LayerPacking.PackedLayers
        (LayerPacking.transposeCells (rect ∪ LayerPacking.layersSupport rowLayers)) colLayers)
      (hrowGap : ∀ i e, entry grown ((rowLayers.get i).1 e, (rowLayers.get i).2 e) =
        entry grown (e, (rowLayers.get i).2 e) + rowGap i e)
      (hcolGap : ∀ i e, entry grown ((colLayers.get i).2 e, (colLayers.get i).1 e) =
        entry grown ((colLayers.get i).2 e, e) + colGap i e)
      (wide : (Fin 3 × Fin n) → Fin (3 * (n / 450)) → ℕ)
      (BR : CenteredNetwork (Fin 3 × Fin n) (Fin rowLayers.length × Fin n)
        (hrowPack.rowPairs grown rowGap hrowGap))
      (BC : CenteredNetwork (Fin 3 × Fin n) (Fin colLayers.length × Fin n)
        (hcolPack.columnPairs grown colGap hcolGap))
      (b₀ : Cell n ≃ Fin (n*n)),
      (∀ edge : Fin 3 × Fin n,
        (∀ j, 0 < wide edge j ∧ 2 ∣ wide edge j ∧
          (∀ network : Bool,
            entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
            entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide edge j) ∧
          (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (wide edge j : ℝ) ∧ (wide edge j : ℝ) < poolMaximum n) ∧
        2 ∣ last + (∑ j ∈ Finset.range 5, selectedBridgeGap batches
          (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge) j) + ∑ j, wide edge j) ∧
      TwoNetworkReferenceInvoice grown b₀ rowLayers colLayers hrowPack hcolPack rowGap colGap
        hrowGap hcolGap BR BC ∧
      (∀ edge, BR.source edge = edge.2 ∧ BC.source edge = edge.2 ∧
        BR.target edge = p edge.1 edge.2 ∧ BC.target edge = p edge.1 edge.2) ∧
      (∀ edge, BR.block edge =
        (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
          (fun x => fwJointActualGridPairIndex rows sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2))) ∧
      (∀ edge, BC.block edge =
        (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
          (fun x => fwJointActualGridPairIndex cols sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2))) ∧
      (∀ edge, BR.radius edge = last +
        (∑ j ∈ Finset.range 5, selectedBridgeGap batches
          (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge) j) + ∑ j, wide edge j) ∧
      (∀ edge, BC.radius edge = BR.radius edge) ∧
      (∀ edge, (∑ k ∈ BR.block edge, (hrowPack.rowPairs grown rowGap hrowGap).gap k) = BR.radius edge ∧
        (∑ k ∈ BC.block edge, (hcolPack.columnPairs grown colGap hcolGap).gap k) = BC.radius edge) ∧
      (∀ r, |2 * (rowSum b₀ r : ℤ) -
        physicalNetworkMidpointTwice (hrowPack.rowPairs grown rowGap hrowGap) BR r| ≤ 9) ∧
      (∀ c, |2 * (columnSum b₀ c : ℤ) -
        physicalNetworkMidpointTwice (hcolPack.columnPairs grown colGap hcolGap) BC c| ≤ 9) ∧
      (∀ edge, 2 * N ≤ BR.radius edge) ∧
         mainSum b₀ = mainSum grown ∧ antiSum b₀ = antiSum grown ∧
         (∀ c ∈ rect, entry b₀ c = entry grown c) ∧
         ∀ fr : Fin 3 × Fin n → ℤ,
         (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((N / 2 : ℕ) : ℤ)) →
         ∀ fc : Fin 3 × Fin n → ℤ,
         (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((N / 2 : ℕ) : ℤ)) →
         ∃ b : Cell n ≃ Fin (n*n),
           (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
             2 * ∑ e : Fin 3 × Fin n, edgeTransfer source target fr e r) ∧
           (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) =
             2 * ∑ e : Fin 3 × Fin n, edgeTransfer source target fc e c) ∧
           mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
           (∀ c ∈ rect, entry b c = entry b₀ c) ∧
           Set.range (entry b) = pool n ∧ Function.Injective (entry b)) := by
  intro hrect hseedrect hwide hs hmax choice
  have hmain := bmor_fw_actual_grids_supplied_flows_with_strong_wide_gap_totals_of_theta_radius_upper
    mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hprime hcount
  dsimp only at hmain ⊢
  refine hmain.imp fun p hp => ⟨hp.1, hp.2.1, ?_⟩
  refine hp.2.2.imp fun batches hbatches => hbatches.imp fun hvalid hcand0 => ?_
  refine hcand0.imp fun candidates hcand1 => hcand1.imp fun hcard hcand2 => ?_
  refine hcand2.imp fun kept hcand3 => hcand3.imp fun hsub hcand4 => ?_
  refine hcand4.imp fun hkept hcand5 => ⟨hcand5.1, hcand5.2.1, hcand5.2.2.1, hcand5.2.2.2.1, ?_⟩
  refine hcand5.2.2.2.2.imp fun rows hrows0 => hrows0.imp fun cols hcols0 => ?_
  refine hcols0.imp fun hr hhr0 => hhr0.imp fun hc hhc0 => ?_
  refine hhc0.imp fun sr hsr0 => hsr0.imp fun sc hsc0 => ?_
  refine hsc0.imp fun hsr hhsr0 => hhsr0.imp fun hsc hhsc0 => ?_
  refine hhsc0.imp fun wr hwr0 => hwr0.imp fun wc hwc0 => ?_
  refine hwc0.imp fun hwr hhwr0 => hhwr0.imp fun hwc hhwc0 => ?_
  refine hhwc0.imp fun blocks hblocks0 => hblocks0.imp fun hlen hhlen0 => ?_
  refine hhlen0.imp fun old hold0 => hold0.imp fun stock hstock0 => ?_
  refine hstock0.imp fun last hlast0 => hlast0.imp fun stages hstages0 => ?_
  refine hstages0.imp fun trace htrace0 => htrace0.imp fun hoff hhoff0 => ?_
  refine hhoff0.imp fun gr hgr0 => hgr0.imp fun gc hgc0 => ?_
  refine hgc0.imp fun hgr hhgr0 => hhgr0.imp fun hgc hhgc0 => ?_
  refine hhgc0.imp fun grown hgrown => ?_
  refine ⟨hgrown.1, hgrown.2.1, hgrown.2.2.1, hgrown.2.2.2.1, hgrown.2.2.2.2.1,
    hgrown.2.2.2.2.2.1, hgrown.2.2.2.2.2.2.1, hgrown.2.2.2.2.2.2.2.1,
    hgrown.2.2.2.2.2.2.2.2.1, hgrown.2.2.2.2.2.2.2.2.2.1, hgrown.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
  have hg1 := hgrown.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨hg1.1, hg1.2.1, hg1.2.2.1, hg1.2.2.2.1, hg1.2.2.2.2.1, hg1.2.2.2.2.2.1,
    hg1.2.2.2.2.2.2.1, hg1.2.2.2.2.2.2.2.1, hg1.2.2.2.2.2.2.2.2.1, hg1.2.2.2.2.2.2.2.2.2.1, ?_⟩
  have hg2 := hg1.2.2.2.2.2.2.2.2.2.2
  refine ⟨hg2.1, hg2.2.1, hg2.2.2.1, hg2.2.2.2.1, hg2.2.2.2.2.1, hg2.2.2.2.2.2.1,
    hg2.2.2.2.2.2.2.1, hg2.2.2.2.2.2.2.2.1, hg2.2.2.2.2.2.2.2.2.1, hg2.2.2.2.2.2.2.2.2.2.1, ?_⟩
  have hg3 := hg2.2.2.2.2.2.2.2.2.2.2
  refine ⟨hg3.1, hg3.2.1, hg3.2.2.1, hg3.2.2.2.1, hg3.2.2.2.2.1, hg3.2.2.2.2.2.1,
    hg3.2.2.2.2.2.2.1, hg3.2.2.2.2.2.2.2.1, hg3.2.2.2.2.2.2.2.2.1, hg3.2.2.2.2.2.2.2.2.2.1, ?_⟩
  have hg4 := hg3.2.2.2.2.2.2.2.2.2.2
  refine ⟨hg4.1, hg4.2.1, hg4.2.2.1, hg4.2.2.2.1, hg4.2.2.2.2.1, hg4.2.2.2.2.2.1,
    hg4.2.2.2.2.2.2.1, hg4.2.2.2.2.2.2.2.1, hg4.2.2.2.2.2.2.2.2.1, ?_⟩
  have hrest := hg4.2.2.2.2.2.2.2.2.2
  refine hrest.imp fun hrowPack hr1 => hr1.imp fun hcolPack hr2 => ?_
  refine hr2.imp fun hrowGap hr3 => hr3.imp fun hcolGap hr4 => ?_
  refine hr4.imp fun wide hr5 => hr5.imp fun BR hr6 => ?_
  refine hr6.imp fun BC hr7 => hr7.imp fun b₀ hr8 => ?_
  have hmidpoints := fw_reference_invoice_physical_midpoint_bounds p grown b₀
    (packedRectangleSupport hs choice) (((rows ++ sr) ++ wr) ++ gr) (((cols ++ sc) ++ wc) ++ gc)
    hrowPack hcolPack
    (fwPhysicalRowLayerGap grown (((rows ++ sr) ++ wr) ++ gr))
    (fwPhysicalColumnLayerGap grown (((cols ++ sc) ++ wc) ++ gc))
    hrowGap hcolGap BR BC hr8.2.2.1
    (fun edge => (hr8.2.2.2.2.2.2.2.1 edge).1) (fun edge => (hr8.2.2.2.2.2.2.2.1 edge).2) hr8.2.1
  exact ⟨hr8.1, hr8.2.1, hr8.2.2.1, hr8.2.2.2.1, hr8.2.2.2.2.1, hr8.2.2.2.2.2.1,
    hr8.2.2.2.2.2.2.1, hr8.2.2.2.2.2.2.2.1, hmidpoints.1, hmidpoints.2, hr8.2.2.2.2.2.2.2.2⟩

end
end Sude
