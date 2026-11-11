import Sude.FWJointStageDerangements
import Sude.FWOrdinaryTagInvoice

/-! Per-stage ordinary-network row and column squared-incidence invoices.
No rectangle, combined mass, or diagonal bound is asserted. -/
namespace Sude
noncomputable section

/-- Three row and three transposed-column layers contribute exactly eighteen
to a row, provided the selected row-layer edge permutations are derangements. -/
theorem physical_row_stage_invoice_eq_eighteen {n P : ℕ}
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = P * 3) (hc : cols.length = P * 3)
    (j : Fin P) (r : Fin n) (hder : ∀ k : Fin 3, ∀ i, (prefixStageLayer rows hr j k).1 i ≠ i) :
    physicalRowStageInvoice rows cols hr hc j r = 18 := by
  have h := LayerPacking.ordinary_stage_row_squared_invoice (d := 6) (s := 3) (by norm_num)
    (fun k => (prefixStageLayer rows hr j k).1) (fun k => (prefixStageLayer rows hr j k).2)
    (fun k => (prefixStageLayer cols hc j k).1) (fun k => (prefixStageLayer cols hc j k).2) hder r
  norm_num at h
  exact h

/-- The column invoice is eighteen when the selected transposed-column
network's edge permutations are derangements. -/
theorem physical_column_stage_invoice_eq_eighteen {n P : ℕ}
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = P * 3) (hc : cols.length = P * 3)
    (j : Fin P) (c : Fin n) (hder : ∀ k : Fin 3, ∀ i, (prefixStageLayer cols hc j k).1 i ≠ i) :
    physicalColumnStageInvoice rows cols hr hc j c = 18 := by
  have h := LayerPacking.ordinary_stage_column_squared_invoice (d := 6) (s := 3) (by norm_num)
    (fun k => (prefixStageLayer rows hr j k).1) (fun k => (prefixStageLayer rows hr j k).2)
    (fun k => (prefixStageLayer cols hc j k).1) (fun k => (prefixStageLayer cols hc j k).2) hder c
  norm_num at h
  exact h

/-- Actual bridge ordinary tags contribute eighteen to each row at this stage. -/
theorem fw_bridge_ordinary_row_stage_eq_eighteen {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (j : Fin 5) (r : Fin n) (hder : ∀ k : Fin 3, ∀ i, (prefixStageLayer rows hr j k).1 i ≠ i) :
    (∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
      (physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc)
        (fun z => z.1 = r) (j, fwPrefixToControllerPair n
          (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
            (network,k,edge)))) ^ 2) = 18 := by
  rw [fw_bridge_reindexed_ordinary_row_stage_invoice]
  exact physical_row_stage_invoice_eq_eighteen rows cols hr hc j r hder

/-- Actual bridge ordinary tags contribute eighteen to each column at this stage. -/
theorem fw_bridge_ordinary_column_stage_eq_eighteen {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (j : Fin 5) (c : Fin n) (hder : ∀ k : Fin 3, ∀ i, (prefixStageLayer cols hc j k).1 i ≠ i) :
    (∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
      (physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc)
        (fun z => z.2 = c) (j, fwPrefixToControllerPair n
          (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
            (network,k,edge)))) ^ 2) = 18 := by
  rw [fw_bridge_reindexed_ordinary_column_stage_invoice]
  exact physical_column_stage_invoice_eq_eighteen rows cols hr hc j c hder

/-- Actual wide ordinary tags contribute eighteen to each row at this stage. -/
theorem fw_wide_ordinary_row_stage_eq_eighteen {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (r : Fin n) (hder : ∀ k : Fin 3, ∀ i, (prefixStageLayer rows hr j k).1 i ≠ i) :
    (∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
      (physicalPairLineWeight (fwWidePhysicalPairCells hwide hs choice rows cols hr hc)
        (fun z => z.1 = r) (j, fwPrefixToControllerPair n
          (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
            (network,k,edge)))) ^ 2) = 18 := by
  rw [fw_wide_reindexed_ordinary_row_stage_invoice]
  exact physical_row_stage_invoice_eq_eighteen rows cols hr hc j r hder

/-- Actual wide ordinary tags contribute eighteen to each column at this stage. -/
theorem fw_wide_ordinary_column_stage_eq_eighteen {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (c : Fin n) (hder : ∀ k : Fin 3, ∀ i, (prefixStageLayer cols hc j k).1 i ≠ i) :
    (∑ network : Fin 2, ∑ k : Fin 3, ∑ edge : Fin n,
      (physicalPairLineWeight (fwWidePhysicalPairCells hwide hs choice rows cols hr hc)
        (fun z => z.2 = c) (j, fwPrefixToControllerPair n
          (prefixOrdinaryPairIndex (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
            (network,k,edge)))) ^ 2) = 18 := by
  rw [fw_wide_reindexed_ordinary_column_stage_invoice]
  exact physical_column_stage_invoice_eq_eighteen rows cols hr hc j c hder


/-- Both jointly packed layer lists supply the actual bridge and wide stage
derangements, hence all four physical ordinary stage invoices are eighteen. -/
theorem fw_joint_bridge_wide_ordinary_stage_eighteen {n : ℕ}
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers reservedCols (((bc ++ sc) ++ wc) ++ gc)) :
    (∀ j : Fin 5, ∀ r, physicalRowStageInvoice br bc hbr hbc j r = 18) ∧
    (∀ j : Fin 5, ∀ c, physicalColumnStageInvoice br bc hbr hbc j c = 18) ∧
    (∀ j : Fin (3 * (n / 450)), ∀ r, physicalRowStageInvoice wr wc hwr hwc j r = 18) ∧
    (∀ j : Fin (3 * (n / 450)), ∀ c, physicalColumnStageInvoice wr wc hwr hwc j c = 18) := by
  obtain ⟨hbrd, hbcd, hwrd, hwcd⟩ := fw_joint_bridge_wide_stage_derangements
    br bc sr sc wr wc gr gc hbr hbc hwr hwc reservedRows reservedCols hrows hcols
  exact ⟨fun j r => physical_row_stage_invoice_eq_eighteen br bc hbr hbc j r (hbrd j),
    fun j c => physical_column_stage_invoice_eq_eighteen br bc hbr hbc j c (hbcd j),
    fun j r => physical_row_stage_invoice_eq_eighteen wr wc hwr hwc j r (hwrd j),
    fun j c => physical_column_stage_invoice_eq_eighteen wr wc hwr hwc j c (hwcd j)⟩

end
end Sude
