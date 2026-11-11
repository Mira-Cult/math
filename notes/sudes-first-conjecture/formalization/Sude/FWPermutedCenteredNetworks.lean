import Sude.FWPermutedJointSupportedGap
import Sude.FWPermutedJointOrientation
import Sude.FWPermutedRadiusCapacity
import Sude.FWJointCenteredNetworksOfRadii

/-! Conditional composition of the reallocated physical grids, orientation,
graph and capacity into centered networks. No placement or flow is proved. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- On the same supplied square, the permuted families yield centered row and
column networks at the exact recomputed per-edge radii. -/
theorem fw_permuted_centered_networks {n L : ℕ}
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
    (rect : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers rect (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc))
    (new : Cell n ≃ Fin (n*n))
    (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8))))
    (hbgap : ∀ j b q, entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,b,q),true)) =
      entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,b,q),false)) +
        ((fwBridgeStageBlock n reserved batches hvalid j (πb j b)).high₁ -
          (fwBridgeStageBlock n reserved batches hvalid j (πb j b)).low₁))
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (hwgap : ∀ j b q, entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,q),true)) =
      entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,b,q),false)) +
        fwPermutedWideSourceGap blocks hlen πw j b)
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
    (radius : ℕ)
    (hinitial : ∀ (edge : Fin 3 × Fin n) (network : Bool),
      CompleteEvenGrid (Finset.univ : Finset (Fin 16 ⊕ Fin stages.length))
        (fwPhysicalEdgeTraceGap new (fwSeedEdgeCells sr sc hsr hsc edge network)
          (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network)) radius)
    (heven : 2 ∣ radius) (hcross : (poolMaximum n : ℝ) / 23 ≤ radius)
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
      radius + (∑ j ∈ Finset.range 5, selectedBridgeGap batches (fwPermutedBridgeIndex πb destination j) j) +
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
          2 * ((n / 450) * poolMaximum n) ≤ BR.radius edge) := by
  classical
  dsimp only
  let R := fun edge : Fin 3 × Fin n =>
    let destination : Fin (3 * (n + 8)) := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge
    radius + (∑ j ∈ Finset.range 5, selectedBridgeGap batches (fwPermutedBridgeIndex πb destination j) j) +
      ∑ j, fwPermutedWideSourceGap blocks hlen πw j destination
  obtain ⟨hrowGap, hcolGap⟩ := fw_permuted_four_family_physical_gap_equations hrect hseed hwide hs choice
    br bc hr hc sr sc hsr hsc wr wc hwr hwc offset hoff gr gc hgr hgc reserved batches hvalid new πb hbgap
    blocks hlen πw hwgap hseedgap hrow hcol
  have hcap : ∀ edge, 2 * ((n / 450) * poolMaximum n) ≤ R edge := by
    intro edge
    exact fw_permuted_radius_capacity μ hX hmlo hmhi blocks hlen hmatched πw πb batches radius edge
  have hgrids (edge : Fin 3 × Fin n) := fw_permuted_joint_physical_grids reserved batches hvalid hrect hwide hs choice
    br bc hr hc sr sc hsr hsc wr wc hwr hwc offset hoff gr gc hgr hgc new πb hbgap blocks hlen πw hwgap
    edge radius (hinitial edge) heven hcross μ hX hmlo hmhi hmatched
  refine ⟨hrowGap, hcolGap, ?_⟩
  exact fw_joint_centered_networks_of_radii new rect p br bc sr sc wr wc gr gc hr hc hsr hsc hwr hwc hgr hgc
    hbrow hbcol hsrow hscol hwrow hwcol hgrow hgcol hrows hcols hrowGap hcolGap R
    (2 * ((n / 450) * poolMaximum n)) hcap (fun edge => ⟨(hgrids edge).1, (hgrids edge).2.1⟩)

end
end Sude
