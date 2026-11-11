import Sude.FWControllerStageReindex
import Sude.PhysicalStageSlots
import Sude.PhysicalPairLineSum

/-! Exact row and column incidences of reindexed bridge and wide ordinary
network tags, with no packing or numerical invoice assumptions. -/
namespace Sude
noncomputable section

/-- Each bridge ordinary tag has its actual row-layer pair incidence. -/
theorem fw_bridge_reindexed_ordinary_row_weight {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (j : Fin 5) (network : Fin 2) (k : Fin 3) (edge r : Fin n) :
    physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc)
      (fun c => c.1 = r)
      (j, fwPrefixToControllerPair n
        (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,k,edge))) =
    if network = 0 then LayerPacking.layerRowWeight (prefixStageLayer rows hr j k).1
      (prefixStageLayer rows hr j k).2 r edge
    else LayerPacking.layerColumnWeight (prefixStageLayer cols hc j k).1
      (prefixStageLayer cols hc j k).2 r edge := by
  classical
  unfold physicalPairLineWeight
  rw [fw_bridge_reindexed_ordinary_cell hrect hs choice rows cols hr hc j network (k,edge) false,
    fw_bridge_reindexed_ordinary_cell hrect hs choice rows cols hr hc j network (k,edge) true]
  fin_cases network <;> simp [fwBridgeLayerCells, fwBridgeLayerIndex, prefixStageLayer,
    LayerPacking.sequenceCell, LayerPacking.layerRowWeight, LayerPacking.layerColumnWeight] <;> split_ifs <;> simp_all

/-- Each bridge ordinary tag has its actual column-layer pair incidence. -/
theorem fw_bridge_reindexed_ordinary_column_weight {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (j : Fin 5) (network : Fin 2) (k : Fin 3) (edge c : Fin n) :
    physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc)
      (fun z => z.2 = c)
      (j, fwPrefixToControllerPair n
        (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,k,edge))) =
    if network = 0 then LayerPacking.layerColumnWeight (prefixStageLayer rows hr j k).1
      (prefixStageLayer rows hr j k).2 c edge
    else LayerPacking.layerRowWeight (prefixStageLayer cols hc j k).1
      (prefixStageLayer cols hc j k).2 c edge := by
  classical
  unfold physicalPairLineWeight
  rw [fw_bridge_reindexed_ordinary_cell hrect hs choice rows cols hr hc j network (k,edge) false,
    fw_bridge_reindexed_ordinary_cell hrect hs choice rows cols hr hc j network (k,edge) true]
  fin_cases network <;> simp [fwBridgeLayerCells, fwBridgeLayerIndex, prefixStageLayer,
    LayerPacking.sequenceCell, LayerPacking.layerRowWeight, LayerPacking.layerColumnWeight] <;> split_ifs <;> simp_all

/-- The bridge ordinary-tag squared row incidence equals its physical stage invoice. -/
theorem fw_bridge_reindexed_ordinary_row_stage_invoice {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (j : Fin 5) (r : Fin n) :
    (∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
      (physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc)
        (fun c => c.1 = r)
        (j, fwPrefixToControllerPair n
          (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
            (network,k,edge)))) ^ 2) = physicalRowStageInvoice rows cols hr hc j r := by
  classical
  simp [fw_bridge_reindexed_ordinary_row_weight, Fin.sum_univ_two, physicalRowStageInvoice, Finset.sum_add_distrib]

/-- The bridge ordinary-tag squared column incidence equals its physical stage invoice. -/
theorem fw_bridge_reindexed_ordinary_column_stage_invoice {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (j : Fin 5) (c : Fin n) :
    (∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
      (physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc)
        (fun z => z.2 = c)
        (j, fwPrefixToControllerPair n
          (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
            (network,k,edge)))) ^ 2) = physicalColumnStageInvoice rows cols hr hc j c := by
  classical
  simp [fw_bridge_reindexed_ordinary_column_weight, Fin.sum_univ_two, physicalColumnStageInvoice, Finset.sum_add_distrib]


theorem fw_wide_reindexed_ordinary_row_weight {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (network : Fin 2) (k : Fin 3) (edge r : Fin n) :
    physicalPairLineWeight (fwWidePhysicalPairCells hwide hs choice rows cols hr hc)
      (fun c => c.1 = r)
      (j, fwPrefixToControllerPair n
        (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,k,edge))) =
    if network = 0 then
      LayerPacking.layerRowWeight (prefixStageLayer rows hr j k).1 (prefixStageLayer rows hr j k).2 r edge
    else
      LayerPacking.layerColumnWeight (prefixStageLayer cols hc j k).1 (prefixStageLayer cols hc j k).2 r edge := by
  classical
  unfold physicalPairLineWeight
  rw [fw_wide_reindexed_ordinary_cell hwide hs choice rows cols hr hc j network (k,edge) false,
      fw_wide_reindexed_ordinary_cell hwide hs choice rows cols hr hc j network (k,edge) true]
  fin_cases network <;> simp [fwWideOrdinaryCells, fwWideLayerIndex, prefixStageLayer,
    LayerPacking.sequenceCell, LayerPacking.layerRowWeight, LayerPacking.layerColumnWeight]

/-- Wide ordinary column incidence in terms of its two network layers. -/
theorem fw_wide_reindexed_ordinary_column_weight {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (network : Fin 2) (k : Fin 3) (edge c : Fin n) :
    physicalPairLineWeight (fwWidePhysicalPairCells hwide hs choice rows cols hr hc)
      (fun z => z.2 = c)
      (j, fwPrefixToControllerPair n
        (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,k,edge))) =
    if network = 0 then
      LayerPacking.layerColumnWeight (prefixStageLayer rows hr j k).1 (prefixStageLayer rows hr j k).2 c edge
    else
      LayerPacking.layerRowWeight (prefixStageLayer cols hc j k).1 (prefixStageLayer cols hc j k).2 c edge := by
  classical
  unfold physicalPairLineWeight
  rw [fw_wide_reindexed_ordinary_cell hwide hs choice rows cols hr hc j network (k,edge) false,
      fw_wide_reindexed_ordinary_cell hwide hs choice rows cols hr hc j network (k,edge) true]
  fin_cases network <;> simp [fwWideOrdinaryCells, fwWideLayerIndex, prefixStageLayer,
    LayerPacking.sequenceCell, LayerPacking.layerRowWeight, LayerPacking.layerColumnWeight]

/-- The squared ordinary row incidence equals its actual stage invoice. -/
theorem fw_wide_reindexed_ordinary_row_stage_invoice {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (r : Fin n) :
    (∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
      (physicalPairLineWeight (fwWidePhysicalPairCells hwide hs choice rows cols hr hc)
        (fun c => c.1 = r)
        (j, fwPrefixToControllerPair n
          (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,k,edge)))) ^ 2) =
    physicalRowStageInvoice rows cols hr hc j r := by
  classical
  simp only [fw_wide_reindexed_ordinary_row_weight, Fin.sum_univ_two, ↓reduceIte,
    physicalRowStageInvoice, Finset.sum_add_distrib]
  norm_num

/-- The squared ordinary column incidence equals its actual stage invoice. -/
theorem fw_wide_reindexed_ordinary_column_stage_invoice {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (c : Fin n) :
    (∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
      (physicalPairLineWeight (fwWidePhysicalPairCells hwide hs choice rows cols hr hc)
        (fun z => z.2 = c)
        (j, fwPrefixToControllerPair n
          (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega) (network,k,edge)))) ^ 2) =
    physicalColumnStageInvoice rows cols hr hc j c := by
  classical
  simp only [fw_wide_reindexed_ordinary_column_weight, Fin.sum_univ_two, ↓reduceIte,
    physicalColumnStageInvoice, Finset.sum_add_distrib]
  norm_num

end
end Sude
