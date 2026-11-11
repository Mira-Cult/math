import Sude.FWBridgeWidePairCells
import Sude.FWWideRoleValueCoverage

/-! Same-square bridge and wide pair-cell values from the supplied physical
placement. No theta existence, concentration or mean estimate is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768

theorem fw_bridge_pair_entry_of_placement {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (a : Cell n ≃ Fin (n * n))
    (endpoint : (Fin 5 × Fin (3 * (n + 8))) × Fin 4 → ℕ)
    (hdiag : ∀ t side, entry a (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      endpoint (fwBridgeDiagonalSlot n (t, side)))
    (hord : ∀ x, entry a (fwBridgeLayerCells rows cols hr hc x) =
      endpoint (fwBridgeOrdinarySlot n x))
    (x : (Fin 5 × Fin (6 * (n + 8))) × Bool) :
    entry a (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc x) =
      endpoint (fwPairControllerEquiv 5 n x) := by
  have hp : ∀ y, entry a (fwBridgePhysicalCells hrect hs choice rows cols hr hc y) =
      endpoint (fwBridgeControllerSlot n y) := by
    intro y
    cases y with
    | inl y => exact hdiag y.1 y.2
    | inr y => exact hord y
  calc
    entry a (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc x) =
        endpoint (fwBridgeControllerSlot n (fwBridgePairCellEquiv n x)) := hp _
    _ = endpoint (fwPairControllerEquiv 5 n x) := by
      simp only [fwBridgePairCellEquiv, Equiv.trans_apply, Equiv.ofBijective_apply_symm_apply]

theorem fw_bridge_pair_entry_oriented {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (a : Cell n ≃ Fin (n * n))
    (endpoint : (Fin 5 × Fin (3 * (n + 8))) × Fin 4 → ℕ)
    (hdiag : ∀ t side, entry a (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      endpoint (fwBridgeDiagonalSlot n (t, side)))
    (hord : ∀ x, entry a (fwBridgeLayerCells rows cols hr hc x) =
      endpoint (fwBridgeOrdinarySlot n x))
    (j : Fin 5) (k : Fin (3 * (n + 8))) (p : Fin 2) (side : Bool) :
    entry a (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc
      ((j, Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8))
        (finProdFinEquiv (k, p))), side)) = endpoint ((j, k), prefixPairCorner p side) := by
  rw [fw_bridge_pair_entry_of_placement hrect hs choice rows cols hr hc a endpoint hdiag hord,
    fw_pair_controller_slot]

/-- The inverse wide controller maps each pair label back to its original stage, block and corner. -/
theorem fw_wide_pair_controller_inverse (n : ℕ)
    (x : (Fin (3 * (n / 450)) × Fin (6 * (n + 8))) × Bool) :
    fwWideControllerSlot n (fwWidePairCellEquiv n x) =
      fwPairControllerEquiv (3 * (n / 450)) n x := by
  change (Equiv.ofBijective (fwWideControllerSlot n) (fwWideControllerSlot_bijective n))
    ((Equiv.ofBijective (fwWideControllerSlot n) (fwWideControllerSlot_bijective n)).symm
      (fwPairControllerEquiv (3 * (n / 450)) n x)) = _
  exact Equiv.apply_symm_apply _ _

/-- Wide pair cells have the supplied same-square block endpoint values. -/
theorem fw_wide_pair_entry_of_placement {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (a : Cell n ≃ Fin (n * n))
    (hplaced : ∀ x : FWWideInputs n, entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    (x : (Fin (3 * (n / 450)) × Fin (6 * (n + 8))) × Bool) :
    entry a (fwWidePhysicalPairCells hwide hs choice rows cols hr hc x) =
      doublePairSequenceEndpoint blocks
        (Fin.cast hlen.symm (finProdFinEquiv (fwPairControllerEquiv (3 * (n / 450)) n x).1),
         (fwPairControllerEquiv (3 * (n / 450)) n x).2) := by
  change entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWidePairCellEquiv n x)) = _
  rw [hplaced]
  simp only [fwWideFlatSlot, fw_wide_pair_controller_inverse]

/-- For a selected physical pair, `p=0` uses corners (0,1), and `p=1` uses (3,2). -/
theorem fw_wide_pair_entry_oriented {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (a : Cell n ≃ Fin (n * n))
    (hplaced : ∀ x : FWWideInputs n, entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    (j : Fin (3 * (n / 450))) (k : Fin (3 * (n + 8))) (p : Fin 2) (side : Bool) :
    entry a (fwWidePhysicalPairCells hwide hs choice rows cols hr hc
      ((j, Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8)) (finProdFinEquiv (k,p))), side)) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (finProdFinEquiv (j,k)), prefixPairCorner p side) := by
  rw [fw_wide_pair_entry_of_placement hwide hs choice rows cols hr hc blocks hlen a hplaced]
  rw [fw_pair_controller_slot]


theorem fw_wide_pair_entry_of_placement_four_corners {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (a : Cell n ≃ Fin (n * n))
    (hplaced : ∀ x : FWWideInputs n, entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    (j : Fin (3 * (n / 450))) (k : Fin (3 * (n + 8))) :
    let idx := Fin.cast hlen.symm (finProdFinEquiv (j,k))
    let v := fun (p : Fin 2) (side : Bool) =>
      entry a (fwWidePhysicalPairCells hwide hs choice rows cols hr hc
        ((j, Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8)) (finProdFinEquiv (k,p))), side))
    v 0 false = doublePairSequenceEndpoint blocks (idx,0) ∧
    v 0 true = doublePairSequenceEndpoint blocks (idx,1) ∧
    v 1 false = doublePairSequenceEndpoint blocks (idx,3) ∧
    v 1 true = doublePairSequenceEndpoint blocks (idx,2) := by
  dsimp only
  constructor
  · simpa only [fw_pair_controller_corners.1] using
      fw_wide_pair_entry_oriented hwide hs choice rows cols hr hc blocks hlen a hplaced j k 0 false
  constructor
  · simpa only [fw_pair_controller_corners.2.1] using
      fw_wide_pair_entry_oriented hwide hs choice rows cols hr hc blocks hlen a hplaced j k 0 true
  constructor
  · simpa only [fw_pair_controller_corners.2.2.1] using
      fw_wide_pair_entry_oriented hwide hs choice rows cols hr hc blocks hlen a hplaced j k 1 false
  · simpa only [fw_pair_controller_corners.2.2.2] using
      fw_wide_pair_entry_oriented hwide hs choice rows cols hr hc blocks hlen a hplaced j k 1 true


/-- With supplied bridge batch placements, the original selected block and
its oriented endpoint are exactly the value at the reindexed physical cell. -/
theorem fw_bridge_selected_pair_entry_oriented {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (initial : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (a : Cell n ≃ Fin (n * n))
    (hdiag : ∀ t side, entry a (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (hord : ∀ x, entry a (fwBridgeLayerCells rows cols hr hc x) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeOrdinarySlot n x))
    (j : Fin 5) (k : Fin (3 * (n + 8))) (p : Fin 2) (side : Bool) :
    entry a (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc
      ((j, Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8))
        (finProdFinEquiv (k, p))), side)) =
      (fwBridgeStageBlock n initial batches hvalid j k).endpoint (prefixPairCorner p side) := by
  exact fw_bridge_pair_entry_oriented hrect hs choice rows cols hr hc a
    (fwBridgeStageEndpoint n initial batches hvalid) hdiag hord j k p side

end
end Sude
