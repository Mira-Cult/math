import Sude.FWPermutedWideGapBounds
import Sude.FWBridgeJointIndex
import Sude.FWWideJointIndex

/-! Transport the reallocated ordinary-edge equations to the same square's
joint row and column layers. Stage-dependent source indices are retained;
no flow, physical grid, or concentration is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 8192

/-- The destination bridge edge's actual joint row and column gaps are its
stage-permuted source gap. -/
theorem fw_permuted_bridge_joint_edge_gap {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (initial : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (new : Cell n ≃ Fin (n*n)) (π : Fin 5 → Equiv.Perm (Fin (3 * (n + 8))))
    (hgap : ∀ j b p, entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,b,p),true)) =
      entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hr hc ((j,b,p),false)) +
        ((fwBridgeStageBlock n initial batches hvalid j (π j b)).high₁ -
          (fwBridgeStageBlock n initial batches hvalid j (π j b)).low₁))
    (j : Fin 5) (k : Fin 3) (e : Fin n) :
    let gap := selectedBridgeGap batches
      (π j (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) (k,e))) j
    fwPhysicalRowLayerGap new (((br ++ sr) ++ wr) ++ gr) (fwBridgeJointLayerIndex br sr wr gr hr j k) e = gap ∧
    fwPhysicalColumnLayerGap new (((bc ++ sc) ++ wc) ++ gc) (fwBridgeJointLayerIndex bc sc wc gc hc j k) e = gap ∧
    entry new (layerPairSlot (((br ++ sr) ++ wr) ++ gr) (fwBridgeJointLayerIndex br sr wr gr hr j k, e) false) ≤
      entry new (layerPairSlot (((br ++ sr) ++ wr) ++ gr) (fwBridgeJointLayerIndex br sr wr gr hr j k, e) true) ∧
    entry new ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (fwBridgeJointLayerIndex bc sc wc gc hc j k, e) false).swap) ≤
      entry new ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (fwBridgeJointLayerIndex bc sc wc gc hc j k, e) true).swap) := by
  dsimp only
  have hrow := fw_permuted_bridge_ordinary_edge_gap hrect hs choice br bc hr hc initial batches hvalid new π hgap j (k,e) false
  have hcol := fw_permuted_bridge_ordinary_edge_gap hrect hs choice br bc hr hc initial batches hvalid new π hgap j (k,e) true
  have horow : entry new (layerPairSlot (((br ++ sr) ++ wr) ++ gr) (fwBridgeJointLayerIndex br sr wr gr hr j k, e) false) ≤
      entry new (layerPairSlot (((br ++ sr) ++ wr) ++ gr) (fwBridgeJointLayerIndex br sr wr gr hr j k, e) true) := by
    rw [fw_bridge_joint_row_cell br sr wr gr bc hr hc, fw_bridge_joint_row_cell br sr wr gr bc hr hc]
    omega
  have hocol : entry new ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (fwBridgeJointLayerIndex bc sc wc gc hc j k, e) false).swap) ≤
      entry new ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (fwBridgeJointLayerIndex bc sc wc gc hc j k, e) true).swap) := by
    rw [fw_bridge_joint_column_cell br bc sc wc gc hr hc, fw_bridge_joint_column_cell br bc sc wc gc hr hc]
    omega
  simp only [fwBridgeLayerCells, Bool.false_eq_true, ↓reduceIte, fwBridgeLayerIndex] at hrow hcol
  change entry new ((br.get (bridgeStageLayerIndex hr j k)).1 e, (br.get (bridgeStageLayerIndex hr j k)).2 e) =
    entry new (e, (br.get (bridgeStageLayerIndex hr j k)).2 e) + _ at hrow
  change entry new ((bc.get (bridgeStageLayerIndex hc j k)).2 e, (bc.get (bridgeStageLayerIndex hc j k)).1 e) =
    entry new ((bc.get (bridgeStageLayerIndex hc j k)).2 e, e) + _ at hcol
  refine ⟨?_, ?_, horow, hocol⟩
  · unfold fwPhysicalRowLayerGap
    rw [fwBridgeJointLayerIndex_get]
    omega
  · unfold fwPhysicalColumnLayerGap
    rw [fwBridgeJointLayerIndex_get]
    omega

/-- A supported bridge stage has exactly the source index used by the
recomputed stage-varying abstract grid. -/
theorem fw_permuted_bridge_index_on_stage {n : ℕ}
    (π : Fin 5 → Equiv.Perm (Fin (3 * (n + 8))))
    (b : Fin (3 * (n + 8))) (j : Fin 5) :
    fwPermutedBridgeIndex π b j = π j b := by
  simp [fwPermutedBridgeIndex, j.isLt]

/-- Both actual wide joint gaps are the permuted matched source gap, which is
positive, even, and lies in the stated real interval. -/
theorem fw_permuted_wide_joint_edge_gap_bounds {n L : ℕ}
    (μ X : ℝ) (hX : 100 ≤ X)
    (hmlo : (243 / 500 : ℝ) * X ≤ μ) (hmhi : μ ≤ (123 / 250 : ℝ) * X)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hr : wr.length = (3 * (n / 450)) * 3) (hc : wc.length = (3 * (n / 450)) * 3)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft μ X) (fwReflectedRight μ X))
      (bmorHighBins (fwReflectedLeft μ X) (fwReflectedRight μ X)))
    (new : Cell n ≃ Fin (n*n))
    (π : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (hgap : ∀ j b p, entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hr hc ((j,b,p),true)) =
      entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hr hc ((j,b,p),false)) +
        fwPermutedWideSourceGap blocks hlen π j b)
    (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) :
    let gap := fwPermutedWideSourceGap blocks hlen π j
      (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) (k,e))
    0 < gap ∧ 2 ∣ gap ∧ (2 / 3 : ℝ) * X ≤ (gap : ℝ) ∧ (gap : ℝ) < X ∧
    fwPhysicalRowLayerGap new (((br ++ sr) ++ wr) ++ gr) (fwWideJointLayerIndex br sr wr gr hr j k) e = gap ∧
    fwPhysicalColumnLayerGap new (((bc ++ sc) ++ wc) ++ gc) (fwWideJointLayerIndex bc sc wc gc hc j k) e = gap ∧
    entry new (layerPairSlot (((br ++ sr) ++ wr) ++ gr) (fwWideJointLayerIndex br sr wr gr hr j k, e) false) ≤
      entry new (layerPairSlot (((br ++ sr) ++ wr) ++ gr) (fwWideJointLayerIndex br sr wr gr hr j k, e) true) ∧
    entry new ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (fwWideJointLayerIndex bc sc wc gc hc j k, e) false).swap) ≤
      entry new ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (fwWideJointLayerIndex bc sc wc gc hc j k, e) true).swap) := by
  dsimp only
  obtain ⟨hp, he, hl, hu, hpair⟩ := fw_permuted_wide_edge_gap_bounds μ X hX hmlo hmhi
    hwide hs choice wr wc hr hc blocks hlen hmatched new π hgap j (k,e)
  dsimp only at hpair
  have hphys := fw_wide_joint_selected_gap hwide hs choice br sr wr gr bc sc wc gc hr hc new j k e _ hpair
  have horow : entry new (layerPairSlot (((br ++ sr) ++ wr) ++ gr) (fwWideJointLayerIndex br sr wr gr hr j k, e) false) ≤
      entry new (layerPairSlot (((br ++ sr) ++ wr) ++ gr) (fwWideJointLayerIndex br sr wr gr hr j k, e) true) := by
    rw [fw_wide_joint_row_cell hwide hs choice br sr wr gr wc hr hc,
      fw_wide_joint_row_cell hwide hs choice br sr wr gr wc hr hc]
    have h := hpair false
    omega
  have hocol : entry new ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (fwWideJointLayerIndex bc sc wc gc hc j k, e) false).swap) ≤
      entry new ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) (fwWideJointLayerIndex bc sc wc gc hc j k, e) true).swap) := by
    rw [fw_wide_joint_column_cell hwide hs choice wr bc sc wc gc hr hc,
      fw_wide_joint_column_cell hwide hs choice wr bc sc wc gc hr hc]
    have h := hpair true
    omega
  exact ⟨hp, he, hl, hu, hphys.1, hphys.2, horow, hocol⟩

end
end Sude
