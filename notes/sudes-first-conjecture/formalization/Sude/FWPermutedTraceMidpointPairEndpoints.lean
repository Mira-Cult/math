import Sude.FWPermutedActiveTraceMidpoint
import Sude.FWPermutedReferencePairEndpoints

/-! Preserve pair endpoints up to reversal on the same fresh trace midpoint reference. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

theorem fw_permuted_active_trace_midpoint_reference_pair_endpoints {n L : ℕ}
    (reserved : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n reserved batches j)
    (hrect : 5 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc : List (LayerPacking.Layer n)) (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    {stages : List BTSelectedStage} (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (new : Cell n ≃ Fin (n*n))
    (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8))))
    (hbgap : ∀ j b p, entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,b,p),true)) =
      entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,b,p),false)) +
        ((fwBridgeStageBlock n reserved batches hvalid j (πb j b)).high₁ -
          (fwBridgeStageBlock n reserved batches hvalid j (πb j b)).low₁))
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (hwgap : ∀ j b p, entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),true)) =
      entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,p),false)) +
        fwPermutedWideSourceGap blocks hlen πw j b)
    {Q : ℕ} {initial final : Finset ℕ} {last : ℕ}
    (trace : BTGrowingTrace 2 Q initial 32 final last stages)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hseedgap : ∀ j i, entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true)) =
      entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) + 2)
    (hrow : ∀ (i : Fin (stages.length * 3)) (e : Fin n),
      entry new (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, true))))) =
      entry new (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e)
    (hcol : ∀ (i : Fin (stages.length * 3)) (e : Fin n),
      entry new (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, true))))) =
      entry new (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e)
    (p : Fin 3 → Equiv.Perm (Fin n)) (rect active : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers rect (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
    (hrowActive : LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ⊆ active)
    (hcolActive : LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc)) ⊆ active)
    (hrowGap : ∀ i e, entry new (((((br ++ sr) ++ wr) ++ gr).get i).1 e,
        ((((br ++ sr) ++ wr) ++ gr).get i).2 e) =
      entry new (e, ((((br ++ sr) ++ wr) ++ gr).get i).2 e) +
        fwPhysicalRowLayerGap new (((br ++ sr) ++ wr) ++ gr) i e)
    (hcolGap : ∀ i e, entry new (((((bc ++ sc) ++ wc) ++ gc).get i).2 e,
        ((((bc ++ sc) ++ wc) ++ gc).get i).1 e) =
      entry new (((((bc ++ sc) ++ wc) ++ gc).get i).2 e, e) +
        fwPhysicalColumnLayerGap new (((bc ++ sc) ++ wc) ++ gc) i e)
    (BR : CenteredNetwork (Fin 3 × Fin n) (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n)
      (hrows.rowPairs new (fwPhysicalRowLayerGap new _) hrowGap))
    (BC : CenteredNetwork (Fin 3 × Fin n) (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n)
      (hcols.columnPairs new (fwPhysicalColumnLayerGap new _) hcolGap))
    (hends : ∀ edge, BR.source edge = edge.2 ∧ BC.source edge = edge.2 ∧
      BR.target edge = p edge.1 edge.2 ∧ BC.target edge = p edge.1 edge.2)
    (hrowBlocks : ∀ edge, BR.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)))
    (hcolBlocks : ∀ edge, BC.block edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)))
    (hradii : ∀ edge,
      let index : Fin (3 * (n + 8)) := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge
      let R := last + (∑ j ∈ Finset.range 5, selectedBridgeGap batches (fwPermutedBridgeIndex πb index j) j) +
        ∑ j, fwPermutedWideSourceGap blocks hlen πw j index
      BR.radius edge = R ∧ BC.radius edge = R)
    (hcapacity : ∀ edge, 2 * ((n / 450) * poolMaximum n) ≤ BR.radius edge) :
    let rows := ((br ++ sr) ++ wr) ++ gr
    let cols := ((bc ++ sc) ++ wc) ++ gc
    let N := (n / 450) * poolMaximum n
    let source : Fin 3 × Fin n → Fin n := fun e => e.2
    let target : Fin 3 × Fin n → Fin n := fun e => p e.1 e.2
    ∃ b₀ : Cell n ≃ Fin (n*n),
      TwoNetworkReferenceInvoice new b₀ rows cols hrows hcols
        (fwPhysicalRowLayerGap new rows) (fwPhysicalColumnLayerGap new cols) hrowGap hcolGap BR BC ∧
      (∀ r, |2 * (rowSum b₀ r : ℤ) -
        physicalNetworkMidpointTwice (hrows.rowPairs new (fwPhysicalRowLayerGap new rows) hrowGap) BR r| ≤ 9) ∧
      (∀ c, |2 * (columnSum b₀ c : ℤ) -
        physicalNetworkMidpointTwice (hcols.columnPairs new (fwPhysicalColumnLayerGap new cols) hcolGap) BC c| ≤ 9) ∧
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
        (∀ c ∉ active, entry b c = entry new c) ∧
        active.image (entry b) = active.image (entry new) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  classical
  dsimp only
  let R := fun edge : Fin 3 × Fin n =>
    let index : Fin (3 * (n + 8)) := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge
    last + (∑ j ∈ Finset.range 5, selectedBridgeGap batches (fwPermutedBridgeIndex πb index j) j) +
      ∑ j, fwPermutedWideSourceGap blocks hlen πw j index
  have hR : ∀ edge, BR.radius edge = R edge ∧ BC.radius edge = R edge ∧
      2 * ((n / 450) * poolMaximum n) ≤ BR.radius edge :=
    fun edge => ⟨(hradii edge).1, (hradii edge).2, hcapacity edge⟩
  have hinitial := fw_reallocated_initial_gap_total trace hseed offset hoff hs choice sr sc hsr hsc gr gc hgr hgc
    new hseedgap hrow hcol
  obtain ⟨b₀, hinvoice, hm, ha, hfixed, houtside, hrowPairs, hcolPairs, hrowEndpoints, hcolEndpoints, himage, hpool, hinj, hflows⟩ :=
    fw_permuted_centered_active_reference_pair_endpoints p new rect active (((br ++ sr) ++ wr) ++ gr) (((bc ++ sc) ++ wc) ++ gc)
      hrows hcols hrowActive hcolActive (fwPhysicalRowLayerGap new _) (fwPhysicalColumnLayerGap new _)
      hrowGap hcolGap BR BC hends R hR
  obtain ⟨hmidrow, hmidcol⟩ := fw_permuted_invoice_physical_midpoint_bounds reserved batches hvalid hrect hwide hs choice
    br bc hr hc sr sc hsr hsc wr wc hwr hwc offset hoff gr gc hgr hgc new πb hbgap blocks hlen πw hwgap
    last hinitial p rect hrows hcols hrowGap hcolGap BR BC hends hrowBlocks hcolBlocks hradii b₀ hinvoice
  exact ⟨b₀, hinvoice, hmidrow, hmidcol, hm, ha, hfixed, houtside, hrowPairs, hcolPairs, hrowEndpoints, hcolEndpoints,
    himage, hpool, hinj, hflows⟩


end
end Sude
