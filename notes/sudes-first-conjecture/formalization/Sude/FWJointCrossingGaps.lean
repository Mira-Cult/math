import Sude.FWJointPhysicalGaps
import Sude.FWJointBridgeSeedGaps
import Sude.FWJointWideGrowthGaps

/-! Derive all concatenated physical layer gap equations from the same
bridge, seed, wide and growth placement witnesses. This does not identify
per-edge grid labels or choose any subset of switches. -/
namespace Sude
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- Existing physical endpoint equations supply natural-valued gaps for every
row and column layer in the combined bridge/seed/wide/growth lists. -/
theorem fw_joint_crossing_physical_gaps {n L : ℕ}
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hav : ∀ x, sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard x ∈
      poolFinset n \ priorBridgeReservation ∅ (Finset.range 5) batches)
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hplace : ∀ x, entry old (fwBridgeLayerCells rows cols hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    (hso : ∀ x, entry old (fwSeedOrdinaryCells sr sc hsr hsc x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x)))
    (hwideGap : ∀ (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n),
      ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
        (∀ network : Bool,
          entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e network true)) =
          entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e network false)) + gap) ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n)
    {stages : List BTSelectedStage} (offset : ℕ)
    (hoff : offset + stages.length * (4 * 6) ≤ L)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (hrow : ∀ (i : Fin (stages.length * 3)) (e : Fin n),
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, true))))) =
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e)
    (hcol : ∀ (i : Fin (stages.length * 3)) (e : Fin n),
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, true))))) =
      entry grown (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e) :
    let rowLayers := ((rows ++ sr) ++ wr) ++ gr
    let colLayers := ((cols ++ sc) ++ wc) ++ gc
    (∀ i e, entry grown ((rowLayers.get i).1 e, (rowLayers.get i).2 e) =
      entry grown (e, (rowLayers.get i).2 e) + fwPhysicalRowLayerGap grown rowLayers i e) ∧
    (∀ i e, entry grown ((colLayers.get i).2 e, (colLayers.get i).1 e) =
      entry grown ((colLayers.get i).2 e, e) + fwPhysicalColumnLayerGap grown colLayers i e) := by
  obtain ⟨hbr, hbc, hsr', hsc'⟩ := fw_preserved_bridge_seed_layers_ordered
    batches hvalid candidates hcard kept hsub hkept hav hrect hseed hwide hs choice rows cols hr hc
    sr sc hsr hsc wr wc hwr hwc old grown hfixed hplace hso
  obtain ⟨hwr', hwc'⟩ := fw_wide_layers_ordered hwide hs choice wr wc hwr hwc grown hwideGap
  obtain ⟨hgr', hgc'⟩ := fw_growth_layers_ordered offset hoff hs choice gr gc hgr hgc grown hrow hcol
  exact fw_four_family_physical_gap_equations grown rows cols sr sc wr wc gr gc
    hbr hbc hsr' hsc' hwr' hwc' hgr' hgc'

end
end Sude
