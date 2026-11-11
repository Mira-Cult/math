import Sude.FWJointSupportedGap

/-! Re-establish supported joint gap identities on a seed-reallocated square.
Bridge and wide entries are explicitly preserved; seed and growth gaps refer
to the new square itself. No sorted seed placement or invoice is assumed. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

theorem fw_joint_supported_gap_after_seed_reallocation {n L : ℕ}
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
    {stages : List BTSelectedStage} (offset : ℕ) (hoff : offset + stages.length * (4 * 6) ≤ L)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (edge : Fin 3 × Fin n) (wide : Fin (3 * (n / 450)) → ℕ)
    (hwidepair : ∀ (j : Fin (3 * (n / 450))) (network : Bool),
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide j)
    (b : Cell n ≃ Fin (n*n))
    (hbridgePreserved : ∀ x, entry b (fwBridgeLayerCells br bc hr hc x) =
      entry grown (fwBridgeLayerCells br bc hr hc x))
    (hwidePreserved : ∀ x : FWWideInputs n,
      entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
        entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x)) :
    let labels := fwJointGridLabels (fwJointPreWideGridLabels stages.length) (3 * (n / 450))
    let index := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (k := 3 * (n + 8)) (by omega) edge
    let rowGap := joinedBridgeGap (fwPhysicalEdgeTraceGap b (fwSeedEdgeCells sr sc hsr hsc edge false)
      (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge false)) batches index
    let colGap := joinedBridgeGap (fwPhysicalEdgeTraceGap b (fwSeedEdgeCells sr sc hsr hsc edge true)
      (fwGrowthEdgeCells offset hoff hs choice gr gc hgr hgc edge true)) batches index
    (∀ x : {x // x ∈ labels},
      fwPhysicalRowLayerGap b (((br ++ sr) ++ wr) ++ gr)
        (fwJointActualGridPairIndex br sr wr gr hr hsr hwr hgr ((x,edge.1),edge.2)).1 edge.2 =
          Sum.elim rowGap wide x.1) ∧
    (∀ x : {x // x ∈ labels},
      fwPhysicalColumnLayerGap b (((bc ++ sc) ++ wc) ++ gc)
        (fwJointActualGridPairIndex bc sc wc gc hc hsc hwc hgc ((x,edge.1),edge.2)).1 edge.2 =
          Sum.elim colGap wide x.1) := by
  have hbplace : ∀ x, entry b (fwBridgeLayerCells br bc hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x) := by
    intro x
    rw [hbridgePreserved x, hfixed]
    · exact hplace x
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hbwide : ∀ (j : Fin (3 * (n / 450))) (network : Bool),
      entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
      entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide j := by
    intro j network
    rw [hwidePreserved, hwidePreserved]
    exact hwidepair j network
  exact fw_joint_supported_gap_eq batches hvalid hrect hseed hwide hs choice br bc hr hc
    sr sc hsr hsc wr wc hwr hwc b b (fun _ _ => rfl) hbplace
    offset hoff gr gc hgr hgc edge wide hbwide

end
end Sude
