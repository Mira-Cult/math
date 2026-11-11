import Sude.FWJointCrossingGaps
import Sude.FWJointNetworkSwitches

/-! Joint ordinary physical switches on the same supplied crossing witness.
This establishes arbitrary subset switchability, not a target flow or line repair. -/
namespace Sude
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-- All four row and column networks may be switched in arbitrary subsets;
physical gaps are derived from the actual supplied placement equations. -/
theorem fw_joint_crossing_toggle_networks {n L : ℕ}
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
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e)
    (hpbr : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hpbc : LayerPacking.PackedLayers (LayerPacking.transposeCells ((packedRectangleSupport hs choice) ∪ LayerPacking.layersSupport rows)) cols)
    (hpsr : LayerPacking.PackedLayers
      (((packedRectangleSupport hs choice) ∪ LayerPacking.layersSupport rows) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) sr)
    (hpsc : LayerPacking.PackedLayers (LayerPacking.transposeCells
      ((((packedRectangleSupport hs choice) ∪ LayerPacking.layersSupport rows) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪
        LayerPacking.layersSupport sr)) sc)
    (hpwr : LayerPacking.PackedLayers
      (((((packedRectangleSupport hs choice) ∪ LayerPacking.layersSupport rows) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪
        LayerPacking.layersSupport sr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport sc)) wr)
    (hpwc : LayerPacking.PackedLayers (LayerPacking.transposeCells
      ((((((packedRectangleSupport hs choice) ∪ LayerPacking.layersSupport rows) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪
        LayerPacking.layersSupport sr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∪
        LayerPacking.layersSupport wr)) wc)
    (hpgr : LayerPacking.PackedLayers
      (((((((packedRectangleSupport hs choice) ∪ LayerPacking.layersSupport rows) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪
        LayerPacking.layersSupport sr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∪
        LayerPacking.layersSupport wr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport wc)) gr)
    (hpgc : LayerPacking.PackedLayers (LayerPacking.transposeCells
      ((((((((packedRectangleSupport hs choice) ∪ LayerPacking.layersSupport rows) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪
        LayerPacking.layersSupport sr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∪
        LayerPacking.layersSupport wr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport wc)) ∪
        LayerPacking.layersSupport gr)) gc)
    (Sr : Finset (Fin (((rows ++ sr) ++ wr) ++ gr).length × Fin n))
    (Sc : Finset (Fin (((cols ++ sc) ++ wc) ++ gc).length × Fin n)) :
    let rowLayers := ((rows ++ sr) ++ wr) ++ gr
    let colLayers := ((cols ++ sc) ++ wc) ++ gc
    let rowGap := fwPhysicalRowLayerGap grown rowLayers
    let colGap := fwPhysicalColumnLayerGap grown colLayers
    ∃ b : Cell n ≃ Fin (n*n),
      (∀ r, (rowSum b r : ℤ) - (rowSum grown r : ℤ) =
        ∑ k ∈ Sr, layerTransfer rowLayers rowGap k r) ∧
      (∀ c, (columnSum b c : ℤ) - (columnSum grown c : ℤ) =
        ∑ k ∈ Sc, layerTransfer colLayers colGap k c) ∧
      mainSum b = mainSum grown ∧ antiSum b = antiSum grown ∧
      (∀ c ∈ packedRectangleSupport hs choice, entry b c = entry grown c) ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  dsimp only
  obtain ⟨hrow', hcol'⟩ := fw_joint_crossing_physical_gaps batches hvalid
    candidates hcard kept hsub hkept hav hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc
    wr wc hwr hwc old grown hfixed hplace hso hwideGap offset hoff gr gc hgr hgc hrow hcol
  exact fw_joint_toggle_networks grown (packedRectangleSupport hs choice) rows cols sr sc wr wc gr gc
    hpbr hpbc hpsr hpsc hpwr hpwc hpgr hpgc
    (fwPhysicalRowLayerGap grown _) (fwPhysicalColumnLayerGap grown _) hrow' hcol' Sr Sc

end
end Sude
