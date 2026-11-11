import Sude.FWPreservedPairGapTraceNetworks
import Sude.FWPreservedEarlyTraceNetworksPairEndpoints

/-! Same fresh trace network reference, retaining unordered network endpoints. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem fw_preserved_pair_gap_trace_networks_pair_endpoints {n L : ℕ}
    (reserved : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n reserved batches j)
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc : List (LayerPacking.Layer n)) (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    {stages : List BTSelectedStage} (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (p : Fin 3 → Equiv.Perm (Fin n))
    (hbrow : br.map Prod.fst = bridgeRepeatedPermutations 5 p)
    (hbcol : bc.map Prod.fst = bridgeRepeatedPermutations 5 p)
    (hsrow : sr.map Prod.fst = bridgeRepeatedPermutations 16 p)
    (hscol : sc.map Prod.fst = bridgeRepeatedPermutations 16 p)
    (hwrow : wr.map Prod.fst = bridgeRepeatedPermutations (3 * (n / 450)) p)
    (hwcol : wc.map Prod.fst = bridgeRepeatedPermutations (3 * (n / 450)) p)
    (hgrow : gr.map Prod.fst = bridgeRepeatedPermutations stages.length p)
    (hgcol : gc.map Prod.fst = bridgeRepeatedPermutations stages.length p)
    (rect active : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers rect (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
    (hrowActive : LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ⊆ active)
    (hcolActive : LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc)) ⊆ active)
    (before new : Cell n ≃ Fin (n*n))
    (hbridgeFixed : ∀ x, entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc x) = entry before (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc x))
    (hwideFixed : ∀ x, entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x) = entry before (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x))
    (hseedFixed : ∀ x, entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x) = entry before (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x))
    (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8))))
    (hbgap : ∀ j b q, entry before (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,b,q),true)) =
      entry before (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,b,q),false)) +
        ((fwBridgeStageBlock n reserved batches hvalid j (πb j b)).high₁ -
          (fwBridgeStageBlock n reserved batches hvalid j (πb j b)).low₁))
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (hwgap : ∀ j b q, entry before (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,q),true)) =
      entry before (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,q),false)) +
        fwPermutedWideSourceGap blocks hlen πw j b)
    (hseedgap : ∀ j i, entry before (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true)) =
      entry before (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) + 2)
    (hpair : ∀ (j : Fin stages.length) (i : Fin (6 * (n + 8))),
      entry new (btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
        offset hoff hs choice gr gc hgr hgc ((j,i),true)) =
      entry new (btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
        offset hoff hs choice gr gc hgr hgc ((j,i),false)) +
        (BTStageTrace.stageAt stages rfl j).gap)
    {Q : ℕ} {initial final : Finset ℕ} {last : ℕ}
    (trace : BTGrowingTrace 2 Q initial 32 final last stages)
    (hcross : (poolMaximum n : ℝ) / 23 ≤ last)
    (μ : ℝ) (hX : (100 : ℝ) ≤ poolMaximum n)
    (hmlo : (243 / 500 : ℝ) * poolMaximum n ≤ μ)
    (hmhi : μ ≤ (123 / 250 : ℝ) * poolMaximum n)
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft μ (poolMaximum n)) (fwReflectedRight μ (poolMaximum n)))
      (bmorHighBins (fwReflectedLeft μ (poolMaximum n)) (fwReflectedRight μ (poolMaximum n)))) :
    let rows := ((br ++ sr) ++ wr) ++ gr
    let cols := ((bc ++ sc) ++ wc) ++ gc
    let R := fun edge : Fin 3 × Fin n =>
      let destination : Fin (3 * (n + 8)) := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge
      last + (∑ j ∈ Finset.range 5, selectedBridgeGap batches (fwPermutedBridgeIndex πb destination j) j) +
        ∑ j, fwPermutedWideSourceGap blocks hlen πw j destination
    ∃ (hrowGap : ∀ i e, entry new ((rows.get i).1 e, (rows.get i).2 e) =
          entry new (e, (rows.get i).2 e) + fwPhysicalRowLayerGap new rows i e)
      (hcolGap : ∀ i e, entry new ((cols.get i).2 e, (cols.get i).1 e) =
          entry new ((cols.get i).2 e, e) + fwPhysicalColumnLayerGap new cols i e),
      let vrow := hrows.rowPairs new (fwPhysicalRowLayerGap new rows) hrowGap
      let vcol := hcols.columnPairs new (fwPhysicalColumnLayerGap new cols) hcolGap
      ∃ (BR : CenteredNetwork (Fin 3 × Fin n) (Fin rows.length × Fin n) vrow)
        (BC : CenteredNetwork (Fin 3 × Fin n) (Fin cols.length × Fin n) vcol),
        (∀ edge, BR.source edge = edge.2 ∧ BC.source edge = edge.2 ∧
          BR.target edge = p edge.1 edge.2 ∧ BC.target edge = p edge.1 edge.2) ∧
        (∀ edge, BR.block edge =
          (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
            (fun x => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2))) ∧
        (∀ edge, BC.block edge =
          (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
            (fun x => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2))) ∧
        (∀ edge, BR.radius edge = R edge ∧ BC.radius edge = R edge ∧
          2 * ((n / 450) * poolMaximum n) ≤ BR.radius edge) ∧
        ∃ b₀ : Cell n ≃ Fin (n*n),
          TwoNetworkReferenceInvoice new b₀ rows cols hrows hcols
            (fwPhysicalRowLayerGap new rows) (fwPhysicalColumnLayerGap new cols)
            hrowGap hcolGap BR BC ∧
          (∀ r, |2 * (rowSum b₀ r : ℤ) - physicalNetworkMidpointTwice vrow BR r| ≤ 9) ∧
          (∀ c, |2 * (columnSum b₀ c : ℤ) - physicalNetworkMidpointTwice vcol BC c| ≤ 9) ∧
          mainSum b₀ = mainSum new ∧ antiSum b₀ = antiSum new ∧
          (∀ c ∈ rect, entry b₀ c = entry new c) ∧
          (∀ c ∉ active, entry b₀ c = entry new c) ∧
          (∀ k, entry b₀ (layerPairSlot rows k false) + entry b₀ (layerPairSlot rows k true) =
            entry new (layerPairSlot rows k false) + entry new (layerPairSlot rows k true)) ∧
          (∀ k, entry b₀ (layerPairSlot cols k false).swap + entry b₀ (layerPairSlot cols k true).swap =
            entry new (layerPairSlot cols k false).swap + entry new (layerPairSlot cols k true).swap) ∧
          (∀ k, (entry b₀ (layerPairSlot rows k false) = entry new (layerPairSlot rows k false) ∧
              entry b₀ (layerPairSlot rows k true) = entry new (layerPairSlot rows k true)) ∨
            (entry b₀ (layerPairSlot rows k false) = entry new (layerPairSlot rows k true) ∧
              entry b₀ (layerPairSlot rows k true) = entry new (layerPairSlot rows k false))) ∧
          (∀ k, (entry b₀ (layerPairSlot cols k false).swap = entry new (layerPairSlot cols k false).swap ∧
              entry b₀ (layerPairSlot cols k true).swap = entry new (layerPairSlot cols k true).swap) ∨
            (entry b₀ (layerPairSlot cols k false).swap = entry new (layerPairSlot cols k true).swap ∧
              entry b₀ (layerPairSlot cols k true).swap = entry new (layerPairSlot cols k false).swap)) ∧
          active.image (entry b₀) = active.image (entry new) ∧
          Set.range (entry b₀) = pool n ∧ Function.Injective (entry b₀) ∧
          ∀ fr : Fin 3 × Fin n → ℤ,
          (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fr e ∧
            fr e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
          ∀ fc : Fin 3 × Fin n → ℤ,
          (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fc e ∧
            fc e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
          ∃ b : Cell n ≃ Fin (n*n),
            (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
              2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fr e r) ∧
            (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) =
              2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fc e c) ∧
            mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
            (∀ c ∈ rect, entry b c = entry b₀ c) ∧
            (∀ c ∉ active, entry b c = entry new c) ∧
            active.image (entry b) = active.image (entry new) ∧
            Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  classical
  obtain ⟨hrow, hcol⟩ := growth_pair_gaps_imply_role_network_gaps
    (P := stages.length) (d := 6) (r := 3) (Q := 6 * (n + 8))
    (by omega) (by omega) (by omega) offset hoff hs choice gr gc hgr hgc new
    (fun j => (BTStageTrace.stageAt stages rfl j).gap) hpair
  exact fw_preserved_early_trace_networks_pair_endpoints reserved batches hvalid hrect hseed hwide hs choice
    br bc hr hc sr sc hsr hsc wr wc hwr hwc offset hoff gr gc hgr hgc p
    hbrow hbcol hsrow hscol hwrow hwcol hgrow hgcol rect active hrows hcols hrowActive hcolActive
    before new hbridgeFixed hwideFixed hseedFixed πb hbgap blocks hlen πw hwgap hseedgap hrow hcol
    trace hcross μ hX hmlo hmhi hmatched


end
end Sude
