import Sude.FWPhysicalDoubleBlockCells
import Sude.MatchedBinPreservedBatch

/-! Same-square common-gap premises for supplied bridge and wide double
blocks. No reallocation, grid, concentration, or witness existence is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768

/-- Both physical bridge pairs use their selected source block's common gap. -/
theorem fw_bridge_physical_double_common_gap {n L : ℕ}
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
    (j : Fin 5) (b : Fin (3 * (n + 8))) (p : Fin 2) :
    let block := fwBridgeStageBlock n initial batches hvalid j b
    entry a (fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc ((j,b,p),true)) =
      entry a (fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc ((j,b,p),false)) +
        (block.high₁ - block.low₁) := by
  dsimp only
  change entry a (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc
    ((j, Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8)) (finProdFinEquiv (b,p))), true)) =
    entry a (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc
    ((j, Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8)) (finProdFinEquiv (b,p))), false)) + _
  rw [fw_bridge_selected_pair_entry_oriented hrect hs choice rows cols hr hc initial batches hvalid a hdiag hord j b p true,
      fw_bridge_selected_pair_entry_oriented hrect hs choice rows cols hr hc initial batches hvalid a hdiag hord j b p false]
  have hv := fwBridgeStageBlock_valid n initial batches hvalid j b
  dsimp only [DoublePair.valid] at hv
  fin_cases p
  · change (fwBridgeStageBlock n initial batches hvalid j b).high₁ =
      (fwBridgeStageBlock n initial batches hvalid j b).low₁ +
        ((fwBridgeStageBlock n initial batches hvalid j b).high₁ - (fwBridgeStageBlock n initial batches hvalid j b).low₁)
    omega
  · change (fwBridgeStageBlock n initial batches hvalid j b).high₂ =
      (fwBridgeStageBlock n initial batches hvalid j b).low₂ +
        ((fwBridgeStageBlock n initial batches hvalid j b).high₁ - (fwBridgeStageBlock n initial batches hvalid j b).low₁)
    omega

/-- Supplied matched selected blocks and their same-square physical placement
produce a positive common gap for both oriented pairs of each wide block. -/
theorem fw_wide_physical_selected_double_gap {n L N : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (low high : Fin N → Finset ℕ)
    (hvalid : ∀ b ∈ blocks, b.MatchedValid low high)
    (a : Cell n ≃ Fin (n * n))
    (hplaced : ∀ x : FWWideInputs n, entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2)) :
    let gap := fun (j : Fin (3 * (n / 450))) (b : Fin (3 * (n + 8))) =>
      let block := blocks.get (Fin.cast hlen.symm (finProdFinEquiv (j,b)))
      block.high₁ - block.low₁
    (∀ j b, 0 < gap j b) ∧
    (∀ j b p, entry a (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc ((j,b,p),true)) =
      entry a (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc ((j,b,p),false)) + gap j b) := by
  dsimp only
  constructor
  · intro j b
    let idx := Fin.cast hlen.symm (finProdFinEquiv (j,b))
    let block := blocks.get idx
    have hv := (hvalid block (List.get_mem blocks idx)).1
    rcases hv with ⟨_, _, _, _, _, _, hfirst, _, _⟩
    exact Nat.sub_pos_of_lt hfirst
  · intro j b p
    let idx := Fin.cast hlen.symm (finProdFinEquiv (j,b))
    let block := blocks.get idx
    have hv := (hvalid block (List.get_mem blocks idx)).1
    rcases hv with ⟨_, _, _, _, _, _, hfirst, hsecond, heq⟩
    have ht := fw_wide_pair_entry_oriented hwide hs choice rows cols hr hc blocks hlen a hplaced j b p true
    have hf := fw_wide_pair_entry_oriented hwide hs choice rows cols hr hc blocks hlen a hplaced j b p false
    change entry a (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc ((j,b,p),true)) = _ at ht
    change entry a (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc ((j,b,p),false)) = _ at hf
    rw [ht, hf]
    change block.endpoint (prefixPairCorner p true) = block.endpoint (prefixPairCorner p false) + (block.high₁ - block.low₁)
    fin_cases p <;> simp [prefixPairCorner, DoublePair.endpoint] <;> omega

end
end Sude
