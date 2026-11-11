import Sude.FWBridgeWideOrdinaryLineMass
import Sude.FWOrdinaryRectangleExclusion
import Sude.FWActiveBridgeWideRectangleMembership
import Sude.PrefixOrdinaryRectangleWeightSplit

/-! The exact ordinary incidence remains twelve after removing all active
rectangle endpoints from each actual bridge/wide stage. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

/-- Each actual bridge stage has exactly twelve non-rectangle entries on
any physical row and any physical column. -/
theorem fw_bridge_stage_rectangle_line_split {n P : ℕ} (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc)) (j : Fin 5) :
    let cells := fwBridgePhysicalPairCells hrect hs choice br bc hbr hbc
    let rect := activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
    (∀ r : Fin n,
      (∑ q, physicalPairLineWeight cells (fun z => z.1 = r) (j,q)) -
        (∑ q, physicalPairLineWeight cells (fun z => z ∈ rect ∧ z.1 = r) (j,q)) = 12) ∧
    (∀ c : Fin n,
      (∑ q, physicalPairLineWeight cells (fun z => z.2 = c) (j,q)) -
        (∑ q, physicalPairLineWeight cells (fun z => z ∈ rect ∧ z.2 = c) (j,q)) = 12) := by
  classical
  dsimp only
  have hdiag (rect : Fin (4*6)) (pair : Fin 2) (side : Bool) :=
    fw_bridge_diagonal_cell_mem_active_rectangle hP hrect hs choice br bc hbr hbc j rect pair side
  have hord (network : Fin 2) (k : Fin 3) (edge : Fin n) (side : Bool) :=
    fw_bridge_ordinary_cell_off_active_rectangle hP hrect hs choice br bc sr sc wr wc gr gc
      hbr hbc hrows hcols j network k edge side
  constructor
  · intro r
    rw [prefix_permuted_ordinary_rectangle_weight_split _ (fwPrefixToControllerPair n) j _ _ hdiag hord]
    exact fw_bridge_ordinary_row_line_mass hrect hs choice br bc hbr hbc j r
  · intro c
    rw [prefix_permuted_ordinary_rectangle_weight_split _ (fwPrefixToControllerPair n) j _ _ hdiag hord]
    exact fw_bridge_ordinary_column_line_mass hrect hs choice br bc hbr hbc j c

/-- Each actual wide stage has exactly twelve non-rectangle entries on
any physical row and any physical column. -/
theorem fw_wide_stage_rectangle_line_split {n P : ℕ} (hP : P ≤ 238)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc)) (j : Fin (3 * (n / 450))) :
    let cells := fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc
    let rect := activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
    (∀ r : Fin n,
      (∑ q, physicalPairLineWeight cells (fun z => z.1 = r) (j,q)) -
        (∑ q, physicalPairLineWeight cells (fun z => z ∈ rect ∧ z.1 = r) (j,q)) = 12) ∧
    (∀ c : Fin n,
      (∑ q, physicalPairLineWeight cells (fun z => z.2 = c) (j,q)) -
        (∑ q, physicalPairLineWeight cells (fun z => z ∈ rect ∧ z.2 = c) (j,q)) = 12) := by
  classical
  dsimp only
  have hdiag (rect : Fin (4*6)) (pair : Fin 2) (side : Bool) :=
    fw_wide_diagonal_cell_mem_active_rectangle hP hwide hs choice wr wc hwr hwc j rect pair side
  have hord (network : Fin 2) (k : Fin 3) (edge : Fin n) (side : Bool) :=
    fw_wide_ordinary_cell_off_active_rectangle hP hwide hs choice br bc sr sc wr wc gr gc
      hwr hwc hrows hcols j network k edge side
  constructor
  · intro r
    rw [prefix_permuted_ordinary_rectangle_weight_split _ (fwPrefixToControllerPair n) j _ _ hdiag hord]
    exact fw_wide_ordinary_row_line_mass hwide hs choice wr wc hwr hwc j r
  · intro c
    rw [prefix_permuted_ordinary_rectangle_weight_split _ (fwPrefixToControllerPair n) j _ _ hdiag hord]
    exact fw_wide_ordinary_column_line_mass hwide hs choice wr wc hwr hwc j c

end
end Sude
