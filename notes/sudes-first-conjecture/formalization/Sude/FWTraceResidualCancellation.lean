import Sude.FWResidualFixedGapCancellation
import Sude.FWSeedGrowthGapUniformity
import Sude.FWGrowthTraceNetworkGaps

/-! On the same role-preserving square, installed seed and growth gaps cancel
the residual ordinary-network corrections. This is a conditional identity,
not a construction or complete-line bound. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- Installed seed pairs and a preserved growth trace discharge the
fixed-gap hypotheses for the row and transposed-column residuals. -/
theorem fw_trace_seed_growth_residual_cancellation
    {g Q n L : ℕ} {initial final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    (hpool : ∀ p ∈ initial, p ∈ pool n)
    (hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ Q) (hdiag : (4 * 6) * 2 ≤ Q)
    (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = stages.length * 3)
    (hbc : bc.length = 5 * 3) (hsc : sc.length = 16 * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (hgc : gc.length = stages.length * 3)
    (old new : Cell n ≃ Fin (n*n))
    (hplaced : ∀ x : PrefixPhysicalInputs stages.length 6 3 n,
      entry old (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
        (trace.poolValues rfl hpool (prefixPhysicalInput hfit hdiag x)).val)
    (hfixed : ∀ x : PrefixPhysicalInputs stages.length 6 3 n,
      entry new (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
        entry old (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x))
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
  have hgrowth := fw_growth_preserved_trace_network_gaps trace hpool hfit hdiag offset hoff hs choice
    br sr wr gr bc sc wc gc hgr hgc old new hplaced hfixed vr vc hslotr hslotc
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
