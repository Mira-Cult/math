import Sude.FWOrdinaryDiagonalAvoidance
import Sude.FWJointPackedOccupancy

/-! Ordinary bridge and wide cells avoid the active rectangle support of the
same joint packing. No value, allocation, or line-discrepancy claim is made. -/
namespace Sude
noncomputable section

/-- A selected sublist's stage cells avoid the packed reserved support. -/
theorem fw_selected_stage_layer_off_reserved {n P K : ℕ} {reserved : Finset (Cell n)}
    {all selected : List (LayerPacking.Layer n)}
    (packed : LayerPacking.PackedLayers reserved all)
    (hsub : ∀ layer, layer ∈ selected → layer ∈ all)
    (hlen : selected.length = P * K) (j : Fin P) (k : Fin K) (edge : Fin n) (side : Bool) :
    LayerPacking.layerCell (prefixStageLayer selected hlen j k).1
      (prefixStageLayer selected hlen j k).2 (edge,side) ∉ reserved := by
  let idx : Fin selected.length := Fin.cast hlen.symm (finProdFinEquiv (j,k))
  have hm := LayerPacking.sequenceCell_mem selected idx (edge,side)
  exact ((packed.each_layer (selected.get idx) (hsub _ (List.get_mem selected idx))).2.1 _ hm).1

/-- Transposed packed columns avoid the untransposed rectangle reservation. -/
theorem fw_selected_stage_layer_swap_off_reserved {n P K : ℕ} {reserved : Finset (Cell n)}
    {all selected : List (LayerPacking.Layer n)}
    (packed : LayerPacking.PackedLayers (LayerPacking.transposeCells reserved) all)
    (hsub : ∀ layer, layer ∈ selected → layer ∈ all)
    (hlen : selected.length = P * K) (j : Fin P) (k : Fin K) (edge : Fin n) (side : Bool) :
    (LayerPacking.layerCell (prefixStageLayer selected hlen j k).1
      (prefixStageLayer selected hlen j k).2 (edge,side)).swap ∉ reserved := by
  have h := fw_selected_stage_layer_off_reserved packed hsub hlen j k edge side
  intro hx
  apply h
  apply Finset.mem_image.mpr
  exact ⟨_, hx, Prod.swap_swap _⟩

/-- All reindexed bridge ordinary endpoints avoid the actual active FW
rectangle support; the entire packed rectangle capacity is reserved. -/
theorem fw_bridge_ordinary_cell_off_active_rectangle {n P : ℕ} (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (j : Fin 5) (network : Fin 2) (k : Fin 3) (edge : Fin n) (side : Bool) :
    fwBridgePhysicalPairCells hrect hs choice br bc hbr hbc
      ((j, fwPrefixToControllerPair n (prefixOrdinaryPairIndex
        (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,k,edge))), side) ∉
      activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP) := by
  have hsub := active_rectangle_support_subset_packed hs choice (fwActiveRectangleLabels n P hP)
  rw [fw_bridge_reindexed_ordinary_cell]
  fin_cases network
  · have h := fw_selected_stage_layer_off_reserved hrows
      (selected := br) (by intro x hx; simp [hx]) hbr j k edge side
    exact fun hx => h (hsub (by simpa [fwBridgeLayerCells, fwBridgeLayerIndex,
      prefixStageLayer, LayerPacking.sequenceCell] using hx))
  · have h := fw_selected_stage_layer_swap_off_reserved hcols
      (selected := bc) (by intro x hx; simp [hx]) hbc j k edge side
    exact fun hx => h (Finset.mem_union_left _ (hsub (by simpa [fwBridgeLayerCells, fwBridgeLayerIndex,
      prefixStageLayer, LayerPacking.sequenceCell] using hx)))

/-- Every reindexed wide ordinary endpoint avoids the same active rectangles. -/
theorem fw_wide_ordinary_cell_off_active_rectangle {n P : ℕ} (hP : P ≤ 238)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (j : Fin (3 * (n / 450))) (network : Fin 2) (k : Fin 3) (edge : Fin n) (side : Bool) :
    fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc
      ((j, fwPrefixToControllerPair n (prefixOrdinaryPairIndex
        (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,k,edge))), side) ∉
      activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP) := by
  have hsub := active_rectangle_support_subset_packed hs choice (fwActiveRectangleLabels n P hP)
  rw [fw_wide_reindexed_ordinary_cell]
  fin_cases network
  · have h := fw_selected_stage_layer_off_reserved hrows
      (selected := wr) (by intro x hx; simp [hx]) hwr j k edge side
    exact fun hx => h (hsub (by simpa [fwWideOrdinaryCells, fwWideLayerIndex,
      prefixStageLayer, LayerPacking.sequenceCell] using hx))
  · have h := fw_selected_stage_layer_swap_off_reserved hcols
      (selected := wc) (by intro x hx; simp [hx]) hwc j k edge side
    exact fun hx => h (Finset.mem_union_left _ (hsub (by simpa [fwWideOrdinaryCells, fwWideLayerIndex,
      prefixStageLayer, LayerPacking.sequenceCell] using hx)))

end
end Sude
