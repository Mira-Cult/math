import Sude.FWSeedFreshRoleValuesRadiusUpper
import Sude.FWReallocatedActiveMidpointInvoice

/-! A fresh active-role reference for the same retained theta witness. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- Retain the prior theta witness and add a fresh centered reference with
physical midpoint bounds and the same active role-value image. No seed
concentration assertion is transferred to the fresh reference. -/
theorem bmor_fw_seed_fresh_active_role_midpoints_of_theta_radius_upper
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
           Set.range (entry b) = pool n ∧ Function.Injective (entry b)) ∧
      (let cells := fwSeedExistingPairCells hseedrect hs choice sr sc hsr hsc
       let line := fun l : Fin ((n+n)+2) => fun c => c ∈ physicalAllLineCells l
       let weights := fun l j q => physicalPairLineWeight cells (line l) (j, q)
       let values := fun j q => (((entry grown (cells ((j, q), false)) : ℝ) +
         entry grown (cells ((j, q), true))) / 2)
       let V : ℝ := (11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2
       let B := Real.sqrt (V * Real.log (4 * (((n + n) + 2 : ℕ) : ℝ)) / 2)
       ∃ (ω : Fin 16 → Equiv.Perm (Fin (6 * (n + 8)))) (b : Cell n ≃ Fin (n*n)),
         (∀ j i side, entry b (cells ((j, i), side)) = entry grown (cells ((j, ω j i), side))) ∧
         (∀ c, c ∉ Set.range cells → entry b c = entry grown c) ∧
         (∀ j, Finset.univ.image (fun x : Fin (6 * (n + 8)) × Bool =>
           entry b (cells ((j, x.1), x.2))) =
           Finset.univ.image (fun x : Fin (6 * (n + 8)) × Bool =>
           entry grown (cells ((j, x.1), x.2)))) ∧
         Finset.univ.image (fun x => entry b (cells x)) =
           retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub ∧
         (∀ j i, entry b (cells ((j, i), true)) = entry b (cells ((j, i), false)) + 2) ∧
         (∀ l, |stageLineCentered (fun _ _ => Finset.univ) weights values l ω| ≤ B) ∧
         (∀ l, |(∑ c ∈ (Finset.univ.image cells).filter (line l), (entry b c : ℝ)) -
           (∑ j, ((∑ q, weights l j q) * ((∑ q, values j q) / ((6 * (n + 8) : ℕ) : ℝ)))) -
           (∑ p, physicalPairLineOrientation cells (line l) p * ((2 : ℝ) / 2))| ≤ B) ∧
         ((fwGrowthEarlyRoleCells hrect hseedrect hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc ∪
           Finset.univ.image (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc)).image (entry b) =
           fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks ∪
             Finset.univ.biUnion (fun j : Fin stages.length => (BTStageTrace.stageAt stages rfl j).footprint)) ∧
         (let rect := packedRectangleSupport hs choice
          let rowLayers := ((rows ++ sr) ++ wr) ++ gr
          let colLayers := ((cols ++ sc) ++ wc) ++ gc
          ∃ (hrowPack₂ : LayerPacking.PackedLayers rect rowLayers)
            (hcolPack₂ : LayerPacking.PackedLayers (LayerPacking.transposeCells
              (rect ∪ LayerPacking.layersSupport rowLayers)) colLayers),
    (∀ t side, entry b (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      entry grown (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side))) ∧
    (∀ x, entry b (fwBridgeLayerCells rows cols hr hc x) = entry grown (fwBridgeLayerCells rows cols hr hc x)) ∧
    (∀ x : FWWideInputs n, entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x)) ∧
    (∀ x : PrefixPhysicalInputs stages.length 6 3 n,
      entry b (btGrowingOffsetCells (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc x) =
      entry grown (btGrowingOffsetCells (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc x)) ∧
    ∃ wide : (Fin 3 × Fin n) → Fin (3 * (n / 450)) → ℕ,
    (∀ edge,
      (∀ j, 0 < wide edge j ∧ 2 ∣ wide edge j ∧
        (∀ network : Bool,
          entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
          entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide edge j) ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (wide edge j : ℝ) ∧ (wide edge j : ℝ) < poolMaximum n) ∧
      (∀ (j : Fin (3 * (n / 450))) (network : Bool),
        entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
        entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide edge j) ∧
      2 ∣ (last + (∑ j ∈ Finset.range 5, selectedBridgeGap batches
        (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge) j) + ∑ j, wide edge j) ∧
      (2 : ℝ) * (n / 450 : ℕ) * (poolMaximum n : ℝ) ≤ ∑ j, (wide edge j : ℝ)) ∧
    (let N := (n / 450) * poolMaximum n
    let source : Fin 3 × Fin n → Fin n := fun e => e.2
    let target : Fin 3 × Fin n → Fin n := fun e => p e.1 e.2
    let rowLayers := ((rows ++ sr) ++ wr) ++ gr
    let colLayers := ((cols ++ sc) ++ wc) ++ gc
    let rowGap := fwPhysicalRowLayerGap b rowLayers
    let colGap := fwPhysicalColumnLayerGap b colLayers
    ∃ (hrowNew : ∀ i e, entry b ((rowLayers.get i).1 e, (rowLayers.get i).2 e) =
          entry b (e, (rowLayers.get i).2 e) + rowGap i e)
      (hcolNew : ∀ i e, entry b ((colLayers.get i).2 e, (colLayers.get i).1 e) =
          entry b ((colLayers.get i).2 e, e) + colGap i e)
      (BR : CenteredNetwork (Fin 3 × Fin n) (Fin rowLayers.length × Fin n)
        (hrowPack₂.rowPairs b rowGap hrowNew))
      (BC : CenteredNetwork (Fin 3 × Fin n) (Fin colLayers.length × Fin n)
        (hcolPack₂.columnPairs b colGap hcolNew))
      (b₀ : Cell n ≃ Fin (n*n)),
      TwoNetworkReferenceInvoice b b₀ rowLayers colLayers hrowPack₂ hcolPack₂ rowGap colGap
        hrowNew hcolNew BR BC ∧
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
      (∀ r, |2 * (rowSum b₀ r : ℤ) -
        physicalNetworkMidpointTwice (hrowPack₂.rowPairs b rowGap hrowNew) BR r| ≤ 9) ∧
      (∀ c, |2 * (columnSum b₀ c : ℤ) -
        physicalNetworkMidpointTwice (hcolPack₂.columnPairs b colGap hcolNew) BC c| ≤ 9) ∧
      (let active := fwGrowthEarlyRoleCells hrect hseedrect hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc ∪
        Finset.univ.image (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc)
       ∃ fresh : Cell n ≃ Fin (n*n),
        TwoNetworkReferenceInvoice b fresh rowLayers colLayers hrowPack₂ hcolPack₂ rowGap colGap
          hrowNew hcolNew BR BC ∧
        (∀ r, |2 * (rowSum fresh r : ℤ) -
          physicalNetworkMidpointTwice (hrowPack₂.rowPairs b rowGap hrowNew) BR r| ≤ 9) ∧
        (∀ c, |2 * (columnSum fresh c : ℤ) -
          physicalNetworkMidpointTwice (hcolPack₂.columnPairs b colGap hcolNew) BC c| ≤ 9) ∧
        mainSum fresh = mainSum b ∧ antiSum fresh = antiSum b ∧
        (∀ c ∈ rect, entry fresh c = entry b c) ∧
        (∀ c ∉ active, entry fresh c = entry b c) ∧
        active.image (entry fresh) = active.image (entry b) ∧
        active.image (entry fresh) = fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks ∪
          Finset.univ.biUnion (fun j : Fin stages.length => (BTStageTrace.stageAt stages rfl j).footprint) ∧
        Set.range (entry fresh) = pool n ∧ Function.Injective (entry fresh) ∧
        ∀ fr : Fin 3 × Fin n → ℤ,
        (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((N / 2 : ℕ) : ℤ)) →
        ∀ fc : Fin 3 × Fin n → ℤ,
        (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((N / 2 : ℕ) : ℤ)) →
        ∃ out : Cell n ≃ Fin (n*n),
          (∀ r, (rowSum out r : ℤ) - (rowSum fresh r : ℤ) =
            2 * ∑ e : Fin 3 × Fin n, edgeTransfer source target fr e r) ∧
          (∀ c, (columnSum out c : ℤ) - (columnSum fresh c : ℤ) =
            2 * ∑ e : Fin 3 × Fin n, edgeTransfer source target fc e c) ∧
          mainSum out = mainSum fresh ∧ antiSum out = antiSum fresh ∧
          (∀ c ∈ rect, entry out c = entry fresh c) ∧
          (∀ c ∉ active, entry out c = entry b c) ∧
          active.image (entry out) = active.image (entry b) ∧
          Set.range (entry out) = pool n ∧ Function.Injective (entry out)) ∧
      (∀ edge, 2 * N ≤ BR.radius edge) ∧
      mainSum b₀ = mainSum b ∧ antiSum b₀ = antiSum b ∧
      (∀ c ∈ rect, entry b₀ c = entry b c) ∧
      ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∃ out : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum out r : ℤ) - (rowSum b₀ r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer source target fr e r) ∧
        (∀ c, (columnSum out c : ℤ) - (columnSum b₀ c : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer source target fc e c) ∧
        mainSum out = mainSum b₀ ∧ antiSum out = antiSum b₀ ∧
        (∀ c ∈ rect, entry out c = entry b₀ c) ∧
        Set.range (entry out) = pool n ∧ Function.Injective (entry out)))) := by
  classical
  dsimp only
  obtain ⟨p, hder, hexp, batches, hvalid, candidates, hcard, kept, hsub, hkept,
    hcand, hvariance, hinj, hav, rows, cols, hr, hc, sr, sc, hsr, hsc,
    wr, wc, hwr, hwc, blocks, hlen, old, stock, last, stages, trace, hoff,
    gr, gc, hgr, hgc, grown, hcap, hstocksub, hstockcard, hq, hmass,
    hcross, hupper, hpairwise, havoidTrace, hnarrow, hfixed,
    hrmap, hcmap, hsrmap, hscmap, hgrmap, hgcmap, hchoiceGrowth,
    hrows, hcols, hbrdisj, hsrows, hscols, hsdisj, hwpack, hjointrow, hjointcol,
    hgrpacked, hgcpacked, hgdisj, hplaced, hdiagGap, hcomplete,
    hbd, hsd, hso, hbo, hrow, hcol, hmatched, hpair, havoid, hwp,
    hwidegap, hwidecoords, hbridgegrid, hwidegrid, hswitch, hseparate, hactual,
    ⟨hrowPack, hcolPack, hrowGap, hcolGap, wide, BR, BC, b₀,
      hw, hinvoice, hends, hblocksR, hblocksC, hradius, hsame, htotals,
      hmidR, hmidC, hcapacity, hm, ha, hrectfixed, hflows⟩,
    ω, b, hperm, hseedFixed, hstage, hset, hgap, hcenter, hselected, hroleValues,
    hrowPack₂, hcolPack₂, hbdPres, hbridgePres, hwidePres, hgrowthPres,
    wide₂, hw₂, hrowNew, hcolNew, BR₂, BC₂, b₀₂,
    hinvoice₂, hends₂, hblocksR₂, hblocksC₂, hradius₂, hsame₂, hmidR₂, hmidC₂, hcapacity₂,
    hm₂, ha₂, hrectfixed₂, hflows₂⟩ :=
    bmor_fw_seed_fresh_midpoints_role_values_of_theta_radius_upper mv bmor upper lower sharp upperSharp
      n hnlo hnhi otherChoice a seeds hseed hprime hcount
  let hrect := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).1
  let hseedrect := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).2.1
  let hwide := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).2.2.1
  let hs := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).2.2.2
  let hmax := fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)
  let choice := fwBridgeSeedRectangleChoice hrect hseedrect
    (fwWideRectangleChoice hwide (fwGrowthRectangleChoice hmax otherChoice))
  let offset := 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)
  have hgrowthEdge : ∀ (edge : Fin 3 × Fin n) (network : Bool) i side,
      entry b (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network i side) =
      entry grown (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network i side) := by
    intro edge network i side
    cases network
    · simpa [fwGrowthEdgeCells] using hgrowthPres
        (Sum.inr (Sum.inl (finProdFinEquiv (i, edge.1), (edge.2, side))))
    · simpa [fwGrowthEdgeCells] using hgrowthPres
        (Sum.inr (Sum.inr (finProdFinEquiv (i, edge.1), (edge.2, side))))
  have hgrowthOld := fun edge network i =>
    fw_growth_edge_gap_of_installation offset hoff hs choice gr gc hgr hgc grown hrow hcol edge network i
  have hwideOld := fun edge j network => ((hw₂ edge).1 j).2.2.1 network
  have hcapacityC : ∀ edge, 2 * ((n / 450) * poolMaximum n) ≤ BC₂.radius edge := by
    intro edge
    rw [hsame₂ edge]
    exact hcapacity₂ edge
  obtain ⟨fresh, hfreshInvoice, hfreshMidR, hfreshMidC, hfreshMain, hfreshAnti, hfreshRect,
    hfreshOutside, hfreshImage, hfreshPool, hfreshInjective, hfreshFlows⟩ :=
    fw_reallocated_active_role_fresh_midpoint_invoice p batches hvalid hrect hseedrect hwide hs choice
      rows cols hr hc sr sc hsr hsc wr wc hwr hwc old grown b hfixed hbo hbridgePres hwidePres hgap
      trace hcap hoff gr gc hgr hgc hgrowthEdge hgrowthOld wide₂ hwideOld
      (packedRectangleSupport hs choice) hrowPack₂ hcolPack₂ hrowNew hcolNew BR₂ BC₂
      hends₂ hblocksR₂ hblocksC₂ hradius₂ hsame₂ ((n / 450) * poolMaximum n) hcapacity₂ hcapacityC
  exact ⟨p, hder, hexp, batches, hvalid, candidates, hcard, kept, hsub, hkept,
    hcand, hvariance, hinj, hav, rows, cols, hr, hc, sr, sc, hsr, hsc,
    wr, wc, hwr, hwc, blocks, hlen, old, stock, last, stages, trace, hoff,
    gr, gc, hgr, hgc, grown, hcap, hstocksub, hstockcard, hq, hmass,
    hcross, hupper, hpairwise, havoidTrace, hnarrow, hfixed,
    hrmap, hcmap, hsrmap, hscmap, hgrmap, hgcmap, hchoiceGrowth,
    hrows, hcols, hbrdisj, hsrows, hscols, hsdisj, hwpack, hjointrow, hjointcol,
    hgrpacked, hgcpacked, hgdisj, hplaced, hdiagGap, hcomplete,
    hbd, hsd, hso, hbo, hrow, hcol, hmatched, hpair, havoid, hwp,
    hwidegap, hwidecoords, hbridgegrid, hwidegrid, hswitch, hseparate, hactual,
    ⟨hrowPack, hcolPack, hrowGap, hcolGap, wide, BR, BC, b₀,
      hw, hinvoice, hends, hblocksR, hblocksC, hradius, hsame, htotals,
      hmidR, hmidC, hcapacity, hm, ha, hrectfixed, hflows⟩,
    ω, b, hperm, hseedFixed, hstage, hset, hgap, hcenter, hselected, hroleValues,
    hrowPack₂, hcolPack₂, hbdPres, hbridgePres, hwidePres, hgrowthPres,
    wide₂, hw₂, hrowNew, hcolNew, BR₂, BC₂, b₀₂,
    hinvoice₂, hends₂, hblocksR₂, hblocksC₂, hradius₂, hsame₂, hmidR₂, hmidC₂,
    ⟨fresh, hfreshInvoice, hfreshMidR, hfreshMidC, hfreshMain, hfreshAnti, hfreshRect,
      hfreshOutside, hfreshImage, hfreshImage.trans hroleValues, hfreshPool, hfreshInjective, hfreshFlows⟩,
    hcapacity₂, hm₂, ha₂, hrectfixed₂, hflows₂⟩

end
end Sude
