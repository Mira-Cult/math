import Sude.FWSeedNetworkMatching
import Sude.FWGrowthJointIndex

/-! Same-square seed and trace-growth gaps on the actual joint network.
These conditional interfaces transport no grids, witnesses, or flow. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

/-- Matching network slots and actual endpoint equations determine the row
network's gap on every seed-band pair. -/
theorem fw_seed_joint_row_network_gap {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (br sr wr gr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (a : Cell n ≃ Fin (n*n))
    (v : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) a)
    (hslot : ∀ t side, rowNetworkSlot v (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (hseedgap : ∀ j q, entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),true)) =
       entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),false)) + 2) :
    ∀ t ∈ fwSeedJointPairImage br sr wr gr hsr, v.gap t = 2 := by
  intro t ht
  obtain ⟨hlo,hhi⟩ := fw_seed_joint_row_side_matching hseed hs choice br sr wr gr sc hsr hsc v hslot t ht
  have he := hseedgap (fwSeedJointToOrdinaryIndex br sr wr gr hsr 0 t).1
    (fwSeedJointToOrdinaryIndex br sr wr gr hsr 0 t).2
  rw [hhi, hlo] at he
  have hv := v.gap_at t
  omega

/-- The same physical seed equations determine the gap in a column network
on the transposed placement. -/
theorem fw_seed_joint_column_network_gap {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr bc sc wc gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (a : Cell n ≃ Fin (n*n))
    (v : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) (LayerPacking.transposePlacement a))
    (hslot : ∀ t side, rowNetworkSlot v (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side)
    (hseedgap : ∀ j q, entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),true)) =
       entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,q),false)) + 2) :
    ∀ t ∈ fwSeedJointPairImage bc sc wc gc hsc, v.gap t = 2 := by
  intro t ht
  obtain ⟨hlo,hhi⟩ := fw_seed_joint_column_side_matching hseed hs choice sr bc sc wc gc hsr hsc v hslot t ht
  have he := hseedgap (fwSeedJointToOrdinaryIndex bc sc wc gc hsc 1 t).1
    (fwSeedJointToOrdinaryIndex bc sc wc gc hsc 1 t).2
  have hv := v.gap_at t
  have hhi' := congrArg Prod.swap hhi
  have hlo' := congrArg Prod.swap hlo
  simp only [Prod.swap_swap] at hhi' hlo'
  rw [hhi', hlo'] at he
  simp only [LayerPacking.entry_transposePlacement] at hv
  simpa only [Prod.swap_prod_mk] using (Nat.add_left_cancel (he.symm.trans hv)).symm


/-- On the same placement, a side-matched network carries the physical gap
of its labelled layer, including the sign encoded by its gap equation. -/
theorem row_network_gap_eq_physical_layer_gap {n : ℕ}
    (layers : List (LayerPacking.Layer n)) (a : Cell n ≃ Fin (n*n))
    (v : RowNetworkPairs (Fin layers.length × Fin n) a)
    (hslot : ∀ t side, rowNetworkSlot v (t,side) = layerPairSlot layers t side)
    (i : Fin layers.length) (e : Fin n) :
    v.gap (i,e) = fwPhysicalRowLayerGap a layers i e := by
  have hlo := congrArg (entry a) (hslot (i,e) false)
  have hhi := congrArg (entry a) (hslot (i,e) true)
  simp only [rowNetworkSlot, Bool.false_eq_true, ↓reduceIte, layerPairSlot,
    LayerPacking.sequenceCell, LayerPacking.layerCell] at hlo hhi
  have hv := v.gap_at (i,e)
  rw [hhi, hlo] at hv
  unfold fwPhysicalRowLayerGap
  omega

/-- On a transposed placement, the row-network gap is the physical column
layer gap in the original placement. -/
theorem column_network_gap_eq_physical_layer_gap {n : ℕ}
    (layers : List (LayerPacking.Layer n)) (a : Cell n ≃ Fin (n*n))
    (v : RowNetworkPairs (Fin layers.length × Fin n) (LayerPacking.transposePlacement a))
    (hslot : ∀ t side, rowNetworkSlot v (t,side) = layerPairSlot layers t side)
    (i : Fin layers.length) (e : Fin n) :
    v.gap (i,e) = fwPhysicalColumnLayerGap a layers i e := by
  have h := row_network_gap_eq_physical_layer_gap layers (LayerPacking.transposePlacement a) v hslot i e
  simpa only [fwPhysicalRowLayerGap, fwPhysicalColumnLayerGap,
    LayerPacking.entry_transposePlacement] using h

/-- Installed growth-stage endpoint equations on the same square force the
actual joint row and column network gaps to be the recorded stage gap, for
every graph edge. Different stages may carry different gaps. -/
theorem fw_growth_joint_network_trace_gaps {n L : ℕ} {stages : List BTSelectedStage}
    (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (a : Cell n ≃ Fin (n*n))
    (vr : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) a)
    (vc : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) (LayerPacking.transposePlacement a))
    (hslotr : ∀ t side, rowNetworkSlot vr (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (hslotc : ∀ t side, rowNetworkSlot vc (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side)
    (hrow : ∀ (i : Fin (stages.length * 3)) (e : Fin n),
      entry a (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, true))))) =
      entry a (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e)
    (hcol : ∀ (i : Fin (stages.length * 3)) (e : Fin n),
      entry a (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, true))))) =
      entry a (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e)
    (j : Fin stages.length) (k : Fin 3) (e : Fin n) :
    vr.gap (fwGrowthJointLayerIndex br sr wr gr hgr j k,e) = (BTStageTrace.stageAt stages rfl j).gap ∧
    vc.gap (fwGrowthJointLayerIndex bc sc wc gc hgc j k,e) = (BTStageTrace.stageAt stages rfl j).gap := by
  obtain ⟨hr,hc⟩ := fw_growth_joint_trace_gap offset hoff hs choice br sr wr gr bc sc wc gc hgr hgc a hrow hcol j k e
  constructor
  · exact (row_network_gap_eq_physical_layer_gap _ a vr hslotr _ e).trans hr
  · exact (column_network_gap_eq_physical_layer_gap _ a vc hslotc _ e).trans hc

end
end Sude
