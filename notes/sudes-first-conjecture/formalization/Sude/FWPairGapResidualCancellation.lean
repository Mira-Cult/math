import Sude.FWResidualFixedGapCancellation
import Sude.FWSeedGrowthGapUniformity
import Sude.FWSeedGrowthNetworkGaps
import Sude.GrowthPairNetworkGapReindex

/-! Same-square seed and stagewise growth pair gaps cancel the residual
ordinary-network corrections, including after stage permutations. This is a
conditional identity, not a construction or complete-line bound. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- Installed seed gaps and stagewise growth pair gaps discharge the fixed-gap
hypotheses for the row and transposed-column residuals on the same square. -/
theorem fw_pair_gap_seed_growth_residual_cancellation
    {n L : ℕ} {stages : List BTSelectedStage}
    (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = stages.length * 3)
    (hbc : bc.length = 5 * 3) (hsc : sc.length = 16 * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (hgc : gc.length = stages.length * 3)
    (new : Cell n ≃ Fin (n*n))
    (hpairgap : ∀ j i, entry new (btGrowingOffsetPairCells
      (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc ((j,i),true)) =
      entry new (btGrowingOffsetPairCells
        (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
        offset hoff hs choice gr gc hgr hgc ((j,i),false)) + (stages.get j).gap)
    (hseedgap : ∀ j q, entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),true)) =
       entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),false)) + 2)
    (vr : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) new)
    (vc : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) (LayerPacking.transposePlacement new))
    (hslotr : ∀ t side, rowNetworkSlot vr (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (hslotc : ∀ t side, rowNetworkSlot vc (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side)
    (blocksR : (Fin 3 × Fin n) → Finset (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n))
    (blocksC : (Fin 3 × Fin n) → Finset (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n))
    (hblockr : ∀ edge, blocksR edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2)))
    (hblockc : ∀ edge, blocksC edge =
      (fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex bc sc wc gc hbc hsc hwc hgc ((x,edge.1),edge.2)))
    (r c : Fin n) :
    (∑ k ∈ (Finset.univ.biUnion blocksR) \ (fwBridgeJointPairImage br sr wr gr hbr ∪
      fwWideJointPairImage br sr wr gr hwr), (rowNetworkDelta vr k r : ℝ)) = 0 ∧
    (∑ k ∈ (Finset.univ.biUnion blocksC) \ (fwBridgeJointPairImage bc sc wc gc hbc ∪
      fwWideJointPairImage bc sc wc gc hwc), (rowNetworkDelta vc k c : ℝ)) = 0 := by
  classical
  have hseedr := fw_seed_joint_row_network_gap hseed hs choice br sr wr gr sc hsr hsc new vr hslotr hseedgap
  have hseedc := fw_seed_joint_column_network_gap hseed hs choice sr bc sc wc gc hsr hsc new vc hslotc hseedgap
  have ⟨hrow,hcol⟩ := growth_pair_gaps_imply_role_network_gaps
    (P := stages.length) (d := 6) (r := 3) (Q := 6 * (n + 8))
    (by omega) (by omega) (by omega) offset hoff hs choice gr gc hgr hgc new
    (fun j => (BTStageTrace.stageAt stages rfl j).gap) hpairgap
  have hgrowth := fw_growth_joint_network_trace_gaps offset hoff hs choice
    br sr wr gr bc sc wc gc hgr hgc new vr vc hslotr hslotc hrow hcol
  obtain ⟨gapR, hgapR⟩ := fw_seed_growth_layer_gap_uniformity br sr wr gr hsr hgr vr.gap
    (fun j => (BTStageTrace.stageAt stages rfl j).gap) hseedr (fun j k e => (hgrowth j k e).1)
  obtain ⟨gapC, hgapC⟩ := fw_seed_growth_layer_gap_uniformity bc sc wc gc hsc hgc vc.gap
    (fun j => (BTStageTrace.stageAt stages rfl j).gap) hseedc (fun j k e => (hgrowth j k e).2)
  constructor
  · exact fw_residual_fixed_gap_row_cancellation_real br sr wr gr hbr hsr hwr hgr vr blocksR hblockr
      gapR (fun i hi e side => hslotr (i,e) side) hgapR r
  · exact fw_residual_fixed_gap_row_cancellation_real bc sc wc gc hbc hsc hwc hgc vc blocksC hblockc
      gapC (fun i hi e side => hslotc (i,e) side) hgapC c

end
end Sude
