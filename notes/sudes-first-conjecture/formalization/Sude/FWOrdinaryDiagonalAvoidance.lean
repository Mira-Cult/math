import Sude.FWControllerStageReindex
import Sude.DiagonalPhysicalInvoice

/-! Ordinary FW network cells avoid both diagonals under the supplied joint
row and column packings. No rectangle invoice or concentration is asserted. -/

namespace Sude
noncomputable section

/-- A stage layer drawn from a supplied packed list avoids both labelled
physical diagonals. The selected sublist need not itself be separately packed. -/
theorem fw_selected_stage_layer_off_diagonals {n P K : ℕ} {reserved : Finset (Cell n)}
    {all selected : List (LayerPacking.Layer n)}
    (packed : LayerPacking.PackedLayers reserved all)
    (hsub : ∀ layer, layer ∈ selected → layer ∈ all)
    (hlen : selected.length = P * K) (j : Fin P) (k : Fin K) (edge : Fin n) (side : Bool) :
    LayerPacking.layerCell (prefixStageLayer selected hlen j k).1
      (prefixStageLayer selected hlen j k).2 (edge,side) ∉ mainCells n ∧
    LayerPacking.layerCell (prefixStageLayer selected hlen j k).1
      (prefixStageLayer selected hlen j k).2 (edge,side) ∉ antiCells n := by
  let idx : Fin selected.length := Fin.cast hlen.symm (finProdFinEquiv (j,k))
  have hm := LayerPacking.sequenceCell_mem selected idx (edge,side)
  have hs := (packed.each_layer (selected.get idx) (hsub _ (List.get_mem selected idx))).2.1 _ hm
  exact ⟨hs.2.1, hs.2.2⟩

/-- Transposed stage-layer cells preserve diagonal avoidance. -/
theorem fw_selected_stage_layer_swap_off_diagonals {n P K : ℕ} {reserved : Finset (Cell n)}
    {all selected : List (LayerPacking.Layer n)}
    (packed : LayerPacking.PackedLayers reserved all)
    (hsub : ∀ layer, layer ∈ selected → layer ∈ all)
    (hlen : selected.length = P * K) (j : Fin P) (k : Fin K) (edge : Fin n) (side : Bool) :
    (LayerPacking.layerCell (prefixStageLayer selected hlen j k).1
      (prefixStageLayer selected hlen j k).2 (edge,side)).swap ∉ mainCells n ∧
    (LayerPacking.layerCell (prefixStageLayer selected hlen j k).1
      (prefixStageLayer selected hlen j k).2 (edge,side)).swap ∉ antiCells n := by
  have h := fw_selected_stage_layer_off_diagonals packed hsub hlen j k edge side
  exact ⟨fun hm => h.1 ((LayerPacking.swap_mem_main _).mp hm),
    fun ha => h.2 ((LayerPacking.swap_mem_anti _).mp ha)⟩

/-- Every ordinary bridge endpoint avoids both diagonals under the actual
joint row and column packing. -/
theorem fw_bridge_ordinary_cell_off_diagonals {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers reservedCols (((bc ++ sc) ++ wc) ++ gc))
    (j : Fin 5) (network : Fin 2) (k : Fin 3) (edge : Fin n) (side : Bool) :
    let cell := fwBridgePhysicalPairCells hrect hs choice br bc hbr hbc
      ((j, fwPrefixToControllerPair n (prefixOrdinaryPairIndex
        (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,k,edge))), side)
    cell ∉ mainCells n ∧ cell ∉ antiCells n := by
  dsimp only
  rw [fw_bridge_reindexed_ordinary_cell]
  fin_cases network
  · have h := fw_selected_stage_layer_off_diagonals hrows
      (selected := br) (by intro x hx; simp [hx]) hbr j k edge side
    simpa [fwBridgeLayerCells, fwBridgeLayerIndex, prefixStageLayer, LayerPacking.sequenceCell] using h
  · have h := fw_selected_stage_layer_swap_off_diagonals hcols
      (selected := bc) (by intro x hx; simp [hx]) hbc j k edge side
    simpa [fwBridgeLayerCells, fwBridgeLayerIndex, prefixStageLayer, LayerPacking.sequenceCell] using h

/-- Every ordinary wide endpoint avoids both diagonals under the same joint
packing; the physical wide rectangle offset is untouched. -/
theorem fw_wide_ordinary_cell_off_diagonals {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers reservedCols (((bc ++ sc) ++ wc) ++ gc))
    (j : Fin (3 * (n / 450))) (network : Fin 2) (k : Fin 3) (edge : Fin n) (side : Bool) :
    let cell := fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc
      ((j, fwPrefixToControllerPair n (prefixOrdinaryPairIndex
        (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,k,edge))), side)
    cell ∉ mainCells n ∧ cell ∉ antiCells n := by
  dsimp only
  rw [fw_wide_reindexed_ordinary_cell]
  fin_cases network
  · have h := fw_selected_stage_layer_off_diagonals hrows
      (selected := wr) (by intro x hx; simp [hx]) hwr j k edge side
    simpa [fwWideOrdinaryCells, fwWideLayerIndex, prefixStageLayer, LayerPacking.sequenceCell] using h
  · have h := fw_selected_stage_layer_swap_off_diagonals hcols
      (selected := wc) (by intro x hx; simp [hx]) hwc j k edge side
    simpa [fwWideOrdinaryCells, fwWideLayerIndex, prefixStageLayer, LayerPacking.sequenceCell] using h


/-- A pair whose two endpoints avoid both diagonals has zero incidence
weight on either diagonal. -/
theorem fw_off_diagonal_pair_weight_zero {n : ℕ} {α : Type*}
    (cells : α × Bool → Cell n) (i : α)
    (hfalse : cells (i,false) ∉ mainCells n ∧ cells (i,false) ∉ antiCells n)
    (htrue : cells (i,true) ∉ mainCells n ∧ cells (i,true) ∉ antiCells n) :
    physicalPairLineWeight cells (fun c => c ∈ mainCells n) i = 0 ∧
      physicalPairLineWeight cells (fun c => c ∈ antiCells n) i = 0 := by
  classical
  simp [physicalPairLineWeight, hfalse.1, hfalse.2, htrue.1, htrue.2]

/-- Reindexed bridge ordinary tags have zero incidence on both diagonals. -/
theorem fw_bridge_ordinary_diagonal_weight_zero {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers reservedCols (((bc ++ sc) ++ wc) ++ gc))
    (j : Fin 5) (network : Fin 2) (k : Fin 3) (edge : Fin n) :
    let cells := fwBridgePhysicalPairCells hrect hs choice br bc hbr hbc
    let index := (j, fwPrefixToControllerPair n (prefixOrdinaryPairIndex
      (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,k,edge)))
    physicalPairLineWeight cells (fun c => c ∈ mainCells n) index = 0 ∧
      physicalPairLineWeight cells (fun c => c ∈ antiCells n) index = 0 := by
  dsimp only
  exact fw_off_diagonal_pair_weight_zero _ _
    (fw_bridge_ordinary_cell_off_diagonals hrect hs choice br bc sr sc wr wc gr gc hbr hbc
      reservedRows reservedCols hrows hcols j network k edge false)
    (fw_bridge_ordinary_cell_off_diagonals hrect hs choice br bc sr sc wr wc gr gc hbr hbc
      reservedRows reservedCols hrows hcols j network k edge true)

/-- Reindexed wide ordinary tags have zero incidence on both diagonals. -/
theorem fw_wide_ordinary_diagonal_weight_zero {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers reservedCols (((bc ++ sc) ++ wc) ++ gc))
    (j : Fin (3 * (n / 450))) (network : Fin 2) (k : Fin 3) (edge : Fin n) :
    let cells := fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc
    let index := (j, fwPrefixToControllerPair n (prefixOrdinaryPairIndex
      (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,k,edge)))
    physicalPairLineWeight cells (fun c => c ∈ mainCells n) index = 0 ∧
      physicalPairLineWeight cells (fun c => c ∈ antiCells n) index = 0 := by
  dsimp only
  exact fw_off_diagonal_pair_weight_zero _ _
    (fw_wide_ordinary_cell_off_diagonals hwide hs choice br bc sr sc wr wc gr gc hwr hwc
      reservedRows reservedCols hrows hcols j network k edge false)
    (fw_wide_ordinary_cell_off_diagonals hwide hs choice br bc sr sc wr wc gr gc hwr hwc
      reservedRows reservedCols hrows hcols j network k edge true)

end
end Sude
