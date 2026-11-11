import Sude.FWPhysicalGridGapTotal

/-! Exact radius accounting for supplied actual FW row and column edge
slots. The chosen physical witness and wide pairs remain explicit inputs. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

theorem fw_actual_joint_grid_gap_totals {n L Q : ℕ}
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc : List (LayerPacking.Layer n)) (hr : br.length = 5 * 3) (hc : bc.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hr hc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hplace : ∀ x, entry old (fwBridgeLayerCells br bc hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    {initial final : Finset ℕ} {last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 Q initial 32 final last stages)
    (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (edge : Fin 3 × Fin n) (wide : Fin (3 * (n / 450)) → ℕ)
    (hwidepair : ∀ (j : Fin (3 * (n / 450))) (network : Bool),
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide j)
    (hseedpair : ∀ network i,
      entry grown (fwSeedEdgeCells sr sc hsr hsc edge network i true) =
      entry grown (fwSeedEdgeCells sr sc hsr hsc edge network i false) + 2)
    (hgrowthpair : ∀ network i,
      entry grown (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network i true) =
      entry grown (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge network i false) +
        (BTStageTrace.stageAt stages rfl i).gap) :
    let labels := fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))
    let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
    let radius := last + (∑ j ∈ Finset.range 5, selectedBridgeGap batches index j) + ∑ j, wide j
    let rows := ((br ++ sr) ++ wr) ++ gr
    let cols := ((bc ++ sc) ++ wc) ++ gc
    let rowSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)
    let colSlot := fun x : {x // x ∈ labels} => fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)
    (∑ k ∈ labels.attach.image rowSlot, fwPhysicalRowLayerGap grown rows k.1 k.2) = radius ∧
    (∑ k ∈ labels.attach.image colSlot, fwPhysicalColumnLayerGap grown cols k.1 k.2) = radius := by
  dsimp only
  obtain ⟨hrowgap, hcolgap⟩ := fw_joint_supported_gap_eq batches hvalid hrect hseed hwide hs choice
    br bc hr hc sr sc hsr hsc wr wc hwr hwc old grown hfixed hplace offset hoff gr gc hgr hgc edge wide hwidepair
  constructor
  · apply fw_physical_joint_grid_actual_total trace grown
      (fwSeedEdgeCells sr sc hsr hsc edge false)
      (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge false)
      (hseedpair false) (hgrowthpair false) (selectedBridgeGap batches _) wide
    · intro x y h
      have hh := fwJointActualGridPairIndex_injective br sr wr gr hr hsr hwr hgr h
      exact congrArg (fun z => z.1.1) hh
    · intro x
      have h := hrowgap x
      rcases x with ⟨(((i | i) | i) | i), hi⟩ <;>
        simpa [fwJointActualGridPairIndex, fwJointGridPairIndex,
          fwJointSupportedPairIndex, joinedBridgeGap] using h
  · apply fw_physical_joint_grid_actual_total trace grown
      (fwSeedEdgeCells sr sc hsr hsc edge true)
      (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge true)
      (hseedpair true) (hgrowthpair true) (selectedBridgeGap batches _) wide
    · intro x y h
      have hh := fwJointActualGridPairIndex_injective bc sc wc gc hc hsc hwc hgc h
      exact congrArg (fun z => z.1.1) hh
    · intro x
      have h := hcolgap x
      rcases x with ⟨(((i | i) | i) | i), hi⟩ <;>
        simpa [fwJointActualGridPairIndex, fwJointGridPairIndex,
          fwJointSupportedPairIndex, joinedBridgeGap] using h

end
end Sude
