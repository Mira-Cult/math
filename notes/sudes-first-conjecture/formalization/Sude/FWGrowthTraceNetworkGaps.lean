import Sude.FWGrowthRoleTraceGaps
import Sude.FWSeedGrowthNetworkGaps

/-! Transfer the gaps of an installed trace to side-matched actual joint
networks on a role-preserving square. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384

/-- On the same reallocated square, each actual growth row and column network
layer carries its recorded trace-stage gap, provided that the labelled
network slots match the physical layer slots. No network is constructed. -/
theorem fw_growth_preserved_trace_network_gaps
    {g Q n L : ℕ} {initial final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    (hpool : ∀ p ∈ initial, p ∈ pool n)
    (hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ Q) (hdiag : (4 * 6) * 2 ≤ Q)
    (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (old new : Cell n ≃ Fin (n*n))
    (hplaced : ∀ x : PrefixPhysicalInputs stages.length 6 3 n,
      entry old (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
        (trace.poolValues rfl hpool (prefixPhysicalInput hfit hdiag x)).val)
    (hfixed : ∀ x : PrefixPhysicalInputs stages.length 6 3 n,
      entry new (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
        entry old (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x))
    (vr : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) new)
    (vc : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) (LayerPacking.transposePlacement new))
    (hslotr : ∀ t side, rowNetworkSlot vr (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (hslotc : ∀ t side, rowNetworkSlot vc (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side) :
    ∀ (j : Fin stages.length) (k : Fin 3) (e : Fin n),
      vr.gap (fwGrowthJointLayerIndex br sr wr gr hgr j k,e) = (BTStageTrace.stageAt stages rfl j).gap ∧
      vc.gap (fwGrowthJointLayerIndex bc sc wc gc hgc j k,e) = (BTStageTrace.stageAt stages rfl j).gap := by
  obtain ⟨hrow, hcol⟩ := bt_growing_preserved_role_network_gaps trace hpool hfit hdiag
    offset hoff hs choice gr gc hgr hgc old new hplaced hfixed
  intro j k e
  exact fw_growth_joint_network_trace_gaps offset hoff hs choice br sr wr gr bc sc wc gc
    hgr hgc new vr vc hslotr hslotc hrow hcol j k e

end
end Sude
