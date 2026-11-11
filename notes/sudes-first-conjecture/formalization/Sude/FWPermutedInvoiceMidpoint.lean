import Sude.FWPermutedPhysicalGapTotals
import Sude.FWPhysicalMidpointInvoice

/-! Same-network invoice to physical midpoint comparison after stage-wise
permutations, with explicit initial total and block/radius identities. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

theorem fw_permuted_invoice_physical_midpoint_bounds {n L : ℕ}
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
    (radius : ℕ)
    (hinitial : ∀ (edge : Fin 3 × Fin n) (network : Bool),
      (∑ i, fwPhysicalEdgeTraceGap new (fwSeedEdgeCells sr sc hsr hsc edge network)
        (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network) (Sum.inl i)) +
      (∑ i, fwPhysicalEdgeTraceGap new (fwSeedEdgeCells sr sc hsr hsc edge network)
        (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network) (Sum.inr i)) = radius)
    (p : Fin 3 → Equiv.Perm (Fin n)) (rect : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers rect (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
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
      let R := radius + (∑ j ∈ Finset.range 5, selectedBridgeGap batches (fwPermutedBridgeIndex πb index j) j) +
        ∑ j, fwPermutedWideSourceGap blocks hlen πw j index
      BR.radius edge = R ∧ BC.radius edge = R)
    (b₀ : Cell n ≃ Fin (n*n))
    (hinvoice : TwoNetworkReferenceInvoice new b₀ (((br ++ sr) ++ wr) ++ gr) (((bc ++ sc) ++ wc) ++ gc)
      hrows hcols (fwPhysicalRowLayerGap new _) (fwPhysicalColumnLayerGap new _) hrowGap hcolGap BR BC) :
    (∀ r, |2 * (rowSum b₀ r : ℤ) -
      physicalNetworkMidpointTwice (hrows.rowPairs new (fwPhysicalRowLayerGap new _) hrowGap) BR r| ≤ 9) ∧
    (∀ c, |2 * (columnSum b₀ c : ℤ) -
      physicalNetworkMidpointTwice (hcols.columnPairs new (fwPhysicalColumnLayerGap new _) hcolGap) BC c| ≤ 9) := by
  classical
  have htotal (edge : Fin 3 × Fin n) := fw_permuted_joint_gap_totals reserved batches hvalid hrect hwide hs choice
    br bc hr hc sr sc hsr hsc wr wc hwr hwc offset hoff gr gc hgr hgc new πb hbgap blocks hlen πw hwgap
    edge radius (hinitial edge)
  have hrowTotal (edge : Fin 3 × Fin n) :
      ∑ k ∈ BR.block edge, (hrows.rowPairs new (fwPhysicalRowLayerGap new _) hrowGap).gap k = BR.radius edge := by
    rw [hrowBlocks edge, (hradii edge).1]
    exact (htotal edge).1
  have hcolTotal (edge : Fin 3 × Fin n) :
      ∑ k ∈ BC.block edge, (hcols.columnPairs new (fwPhysicalColumnLayerGap new _) hcolGap).gap k = BC.radius edge := by
    rw [hcolBlocks edge, (hradii edge).2]
    exact (htotal edge).2
  exact fw_reference_invoice_physical_midpoint_bounds p new b₀ rect
    (((br ++ sr) ++ wr) ++ gr) (((bc ++ sc) ++ wc) ++ gc) hrows hcols
    (fwPhysicalRowLayerGap new _) (fwPhysicalColumnLayerGap new _) hrowGap hcolGap BR BC
    hends hrowTotal hcolTotal hinvoice

end
end Sude
