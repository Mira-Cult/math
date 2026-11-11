import Sude.FWGrowthEarlyGeometry
import Sude.FWWheelWitnessTraceStock

/-! Value membership for the actual earlier role cells. No new selection or
physical growth installation is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- Every actual bridge, retained-seed, and wide role cell contains a value
in the early reservation formed from those same selected witnesses. -/
theorem fw_growth_early_role_values {n L : ℕ}
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (a : Cell n ≃ Fin (n*n))
    (hbd : ∀ t side, entry a (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (hbo : ∀ x, entry a (fwBridgeLayerCells rows cols hr hc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    (hsd : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      entry a (packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2)) =
        sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
          (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (prefixRectangleInput (by omega) x)))
    (hso : ∀ x, entry a (fwSeedOrdinaryCells sr sc hsr hsc x) =
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept (fwSeedOrdinaryInput n x)))
    (hwp : ∀ x : FWWideInputs n, entry a (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2)) :
    ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc,
      entry a c ∈ fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks := by
  have hseedMem (x : (Fin 16 × Fin (6 * (n + 8))) × Bool) :
      sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard
        (retainedSeedSlot 17 16 (6 * (n + 8)) kept hsub hkept x) ∈
          retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub := by
    rw [← retainedSeedSlot_image candidates 17 16 (6 * (n + 8)) 2 hcard kept hsub hkept hinj]
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  intro c hc'
  rcases Finset.mem_union.mp hc' with hbseed | hwide'
  · rcases Finset.mem_union.mp hbseed with hb | hseed'
    · rcases Finset.mem_union.mp hb with hd | ho
      · obtain ⟨⟨t, side⟩, _, rfl⟩ := Finset.mem_image.mp hd
        rw [hbd t side]
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (fwBridgeStageEndpoint_mem_final_reservation n batches hvalid _))
      · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ho
        rw [hbo x]
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (fwBridgeStageEndpoint_mem_final_reservation n batches hvalid _))
    · rcases Finset.mem_union.mp hseed' with hd | ho
      · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hd
        rw [hsd x]
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (hseedMem _))
      · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ho
        rw [hso x]
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (hseedMem _))
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hwide'
    rw [hwp x]
    apply Finset.mem_union_right
    apply doublePair_footprint_subset_batch blocks _ (List.get_mem blocks _)
    exact DoublePair.endpoint_mem _ _

end
end Sude
