import Sude.FWControllerStageReindex
import Sude.PrefixRectangleInvoice

/-! Reindexed bridge rectangle pair incidences and their global row/column
invoices. The ordinary network contribution is not included. -/
namespace Sude
noncomputable section

/-- The reindexed physical bridge rectangle pair has precisely the existing
prefix rectangle pair's line-incidence weight. -/
theorem fw_bridge_reindexed_rectangle_pair_weight {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (line : Cell n → Prop) (j : Fin 5) (rect : Fin (4 * 6)) (pair : Fin 2) :
    physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc) line
      (j, fwPrefixToControllerPair n
        (prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair))) =
    rectanglePairWeight hs choice line (prefixRectanglePairSlot hrect ((j,rect),pair)) := by
  classical
  unfold physicalPairLineWeight rectanglePairWeight prefixRectanglePairSlot
  rw [fw_bridge_reindexed_diagonal_cell hrect hs choice rows cols hr hc j rect pair false,
      fw_bridge_reindexed_diagonal_cell hrect hs choice rows cols hr hc j rect pair true]
  rfl

/-- The complete bridge rectangle family contributes at most four to any
row's squared pair-incidence invoice, with arbitrary rectangle choice. -/
theorem fw_bridge_reindexed_rectangle_row_invoice {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (r : Fin n) :
    (∑ j : Fin 5, ∑ rect : Fin (4 * 6), ∑ pair : Fin 2,
      (physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc)
        (fun c => c.1 = r) (j, fwPrefixToControllerPair n
          (prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair)))) ^ 2) ≤ 4 := by
  classical
  simp_rw [fw_bridge_reindexed_rectangle_pair_weight]
  simpa [Fintype.sum_prod_type] using prefixRectangle_row_pair_invoice hrect hs choice r

/-- The complete bridge rectangle family has the same global column invoice. -/
theorem fw_bridge_reindexed_rectangle_column_invoice {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (c : Fin n) :
    (∑ j : Fin 5, ∑ rect : Fin (4 * 6), ∑ pair : Fin 2,
      (physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc)
        (fun z => z.2 = c) (j, fwPrefixToControllerPair n
          (prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair)))) ^ 2) ≤ 4 := by
  classical
  simp_rw [fw_bridge_reindexed_rectangle_pair_weight]
  simpa [Fintype.sum_prod_type] using prefixRectangle_column_pair_invoice hrect hs choice c

end
end Sude
