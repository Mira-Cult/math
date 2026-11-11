import Sude.FWPermutedJointSupportedGap
import Sude.FWJointGridGapTotal

/-! Exact physical block totals for stage-permuted bridge and wide gaps.
The initial seed/growth total is explicitly supplied. No midpoint bound,
concentration, flow or theta witness is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

theorem fw_permuted_joint_gap_totals {n L : ℕ}
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
    (edge : Fin 3 × Fin n) (radius : ℕ)
    (hinitial : ∀ network : Bool,
      (∑ i, fwPhysicalEdgeTraceGap new (fwSeedEdgeCells sr sc hsr hsc edge network)
        (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network) (Sum.inl i)) +
      (∑ i, fwPhysicalEdgeTraceGap new (fwSeedEdgeCells sr sc hsr hsc edge network)
        (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network) (Sum.inr i)) = radius) :
    let index : Fin (3 * (n + 8)) := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge
    let R := radius + (∑ j ∈ Finset.range 5, selectedBridgeGap batches (fwPermutedBridgeIndex πb index j) j) +
      ∑ j, fwPermutedWideSourceGap blocks hlen πw j index
    let labels := fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))
    let rowSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)
    let colSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)
    (∑ x ∈ labels.attach.image rowSlot, fwPhysicalRowLayerGap new (((br ++ sr) ++ wr) ++ gr) x.1 x.2) = R ∧
    (∑ x ∈ labels.attach.image colSlot, fwPhysicalColumnLayerGap new (((bc ++ sc) ++ wc) ++ gc) x.1 x.2) = R := by
  classical
  dsimp only
  let index : Fin (3 * (n + 8)) := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge
  let labels := fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))
  let rowSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)
  let colSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)
  let seed := fun network i => fwPhysicalEdgeTraceGap new (fwSeedEdgeCells sr sc hsr hsc edge network)
    (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network) (Sum.inl i)
  let growth := fun network i => fwPhysicalEdgeTraceGap new (fwSeedEdgeCells sr sc hsr hsc edge network)
    (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network) (Sum.inr i)
  let bridge := fun j => selectedBridgeGap batches (fwPermutedBridgeIndex πb index j) j
  let wide := fun j => fwPermutedWideSourceGap blocks hlen πw j index
  have hrinj : Function.Injective rowSlot := by
    intro x y heq
    have h := fwJointActualGridPairIndex_injective br sr wr gr hr hsr hwr hgr heq
    exact congrArg (fun z => z.1.1) h
  have hcinj : Function.Injective colSlot := by
    intro x y heq
    have h := fwJointActualGridPairIndex_injective bc sc wc gc hc hsc hwc hgc heq
    exact congrArg (fun z => z.1.1) h
  obtain ⟨hrow, hcol⟩ := fw_permuted_joint_supported_gap reserved batches hvalid hrect hwide hs choice
    br bc hr hc sr sc hsr hsc wr wc hwr hwc offset hoff gr gc hgr hgc new πb hbgap blocks hlen πw hwgap edge
  have hrgap (x : {x // x ∈ labels}) :
      fwPhysicalRowLayerGap new (((br ++ sr) ++ wr) ++ gr) (rowSlot x).1 (rowSlot x).2 =
        Sum.elim (Sum.elim (Sum.elim (seed false) (growth false)) bridge) wide x.val := by
    change fwPhysicalRowLayerGap new (((br ++ sr) ++ wr) ++ gr) (rowSlot x).1 edge.2 = _
    have h := hrow x
    rcases x with ⟨(((i | i) | i) | i), hi⟩ <;>
      simpa [rowSlot, seed, growth, bridge, wide, index, fwStageVaryingJoinedBridgeGap,
        fwPhysicalEdgeTraceGap] using h
  have hcgap (x : {x // x ∈ labels}) :
      fwPhysicalColumnLayerGap new (((bc ++ sc) ++ wc) ++ gc) (colSlot x).1 (colSlot x).2 =
        Sum.elim (Sum.elim (Sum.elim (seed true) (growth true)) bridge) wide x.val := by
    change fwPhysicalColumnLayerGap new (((bc ++ sc) ++ wc) ++ gc) (colSlot x).1 edge.2 = _
    have h := hcol x
    rcases x with ⟨(((i | i) | i) | i), hi⟩ <;>
      simpa [colSlot, seed, growth, bridge, wide, index, fwStageVaryingJoinedBridgeGap,
        fwPhysicalEdgeTraceGap] using h
  have hr := fw_joint_grid_gap_total_on_slots (seed false) (growth false) bridge wide rowSlot
    (fun x => fwPhysicalRowLayerGap new (((br ++ sr) ++ wr) ++ gr) x.1 x.2) hrinj hrgap
  have hc := fw_joint_grid_gap_total_on_slots (seed true) (growth true) bridge wide colSlot
    (fun x => fwPhysicalColumnLayerGap new (((bc ++ sc) ++ wc) ++ gc) x.1 x.2) hcinj hcgap
  rw [hinitial false] at hr
  rw [hinitial true] at hc
  exact ⟨hr, hc⟩

end
end Sude
