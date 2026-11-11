import Sude.FWOrdinaryTagInvoice
import Sude.FWSeedLineIncidence

/-! Exact ordinary-stage physical incidence for the block-major bridge and
wide controllers, reindexed to their actual network tags. -/
namespace Sude
noncomputable section

/-- Each bridge stage contributes twelve ordinary entries per physical row. -/
theorem fw_bridge_ordinary_row_line_mass {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (j : Fin 5) (r : Fin n) :
    (∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
      physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc)
        (fun c => c.1 = r) (j, fwPrefixToControllerPair n
          (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
            (network,k,edge)))) = 12 := by
  classical
  simp [fw_bridge_reindexed_ordinary_row_weight, Fin.sum_univ_two, layer_row_weight_sum,
    layer_column_weight_sum]
  <;> norm_num

/-- Each bridge stage contributes twelve ordinary entries per physical column. -/
theorem fw_bridge_ordinary_column_line_mass {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (j : Fin 5) (c : Fin n) :
    (∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
      physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc)
        (fun z => z.2 = c) (j, fwPrefixToControllerPair n
          (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
            (network,k,edge)))) = 12 := by
  classical
  simp [fw_bridge_reindexed_ordinary_column_weight, Fin.sum_univ_two, layer_row_weight_sum,
    layer_column_weight_sum]
  <;> norm_num

/-- Each wide stage contributes twelve ordinary entries per physical row. -/
theorem fw_wide_ordinary_row_line_mass {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (r : Fin n) :
    (∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
      physicalPairLineWeight (fwWidePhysicalPairCells hwide hs choice rows cols hr hc)
        (fun c => c.1 = r) (j, fwPrefixToControllerPair n
          (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
            (network,k,edge)))) = 12 := by
  classical
  simp [fw_wide_reindexed_ordinary_row_weight, Fin.sum_univ_two, layer_row_weight_sum,
    layer_column_weight_sum]
  <;> norm_num

/-- Each wide stage contributes twelve ordinary entries per physical column. -/
theorem fw_wide_ordinary_column_line_mass {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (c : Fin n) :
    (∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
      physicalPairLineWeight (fwWidePhysicalPairCells hwide hs choice rows cols hr hc)
        (fun z => z.2 = c) (j, fwPrefixToControllerPair n
          (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
            (network,k,edge)))) = 12 := by
  classical
  simp [fw_wide_reindexed_ordinary_column_weight, Fin.sum_univ_two, layer_row_weight_sum,
    layer_column_weight_sum]
  <;> norm_num

end
end Sude
