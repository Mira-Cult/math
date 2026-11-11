import Sude.FWControllerStageReindex
import Sude.FWStageVaryingBridgeGrid
import Sude.FWWideEdgeRoles

/-! Exact source-indexed ordinary edge gaps after supplied bridge and wide
double-block permutations. Numeric wide bounds and grid transport are separate. -/

namespace Sude
noncomputable section

/-- The grouped bridge block's network pair is the actual ordinary edge
cell, preserving low/high endpoint orientation. -/
theorem fw_bridge_double_ordinary_cell {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (j : Fin 5) (network : Fin 2) (edge : Fin 3 × Fin n) (side : Bool) :
    fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc
      ((j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge, network), side) =
      fwBridgeLayerCells rows cols hr hc ((j,edge),(decide (network = 1),side)) := by
  have h := fw_bridge_reindexed_ordinary_cell hrect hs choice rows cols hr hc j network edge side
  rw [fwPrefixToControllerPair_ordinary] at h
  exact h

/-- The grouped wide block's network pair is the actual ordinary edge cell. -/
theorem fw_wide_double_ordinary_cell {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (network : Fin 2) (edge : Fin 3 × Fin n) (side : Bool) :
    fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc
      ((j, bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge, network), side) =
      fwWidePhysicalCells hwide hs choice rows cols hr hc
        (fwWideEdgeRole n j edge.1 edge.2 (decide (network = 1)) side) := by
  have h := fw_wide_reindexed_ordinary_cell hwide hs choice rows cols hr hc j network edge side
  rw [fwPrefixToControllerPair_ordinary] at h
  exact h

/-- For each reallocated bridge edge, both physical network pairs use the
permuted source block's actual selected bridge gap. -/
theorem fw_permuted_bridge_ordinary_edge_gap {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (initial : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (new : Cell n ≃ Fin (n*n)) (π : Fin 5 → Equiv.Perm (Fin (3 * (n + 8))))
    (hgap : ∀ j b p, entry new (fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc ((j,b,p),true)) =
      entry new (fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc ((j,b,p),false)) +
        ((fwBridgeStageBlock n initial batches hvalid j (π j b)).high₁ -
          (fwBridgeStageBlock n initial batches hvalid j (π j b)).low₁))
    (j : Fin 5) (edge : Fin 3 × Fin n) (network : Bool) :
    entry new (fwBridgeLayerCells rows cols hr hc ((j,edge),(network,true))) =
      entry new (fwBridgeLayerCells rows cols hr hc ((j,edge),(network,false))) +
        selectedBridgeGap batches (π j (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge)) j := by
  rw [fwBridgeStageBlock_gap n initial batches hvalid]
  cases network
  · have h := hgap j (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge) 0
    rw [fw_bridge_double_ordinary_cell, fw_bridge_double_ordinary_cell] at h
    exact h
  · have h := hgap j (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge) 1
    rw [fw_bridge_double_ordinary_cell, fw_bridge_double_ordinary_cell] at h
    exact h

/-- For each reallocated wide edge, both physical network pairs use the
same permuted source block's exact gap. -/
theorem fw_permuted_wide_ordinary_edge_gap {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (new : Cell n ≃ Fin (n*n))
    (π : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (hgap : ∀ j b p, entry new (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc ((j,b,p),true)) =
      entry new (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc ((j,b,p),false)) +
        ((blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,π j b)))).high₁ -
          (blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,π j b)))).low₁))
    (j : Fin (3 * (n / 450))) (edge : Fin 3 × Fin n) (network : Bool) :
    let source := blocks.get (Fin.cast hlen.symm (finProdFinEquiv
      (j, π j (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge))))
    entry new (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
      entry new (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j edge.1 edge.2 network false)) +
        (source.high₁ - source.low₁) := by
  dsimp only
  cases network
  · have h := hgap j (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge) 0
    rw [fw_wide_double_ordinary_cell, fw_wide_double_ordinary_cell] at h
    exact h
  · have h := hgap j (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge) 1
    rw [fw_wide_double_ordinary_cell, fw_wide_double_ordinary_cell] at h
    exact h

end
end Sude
