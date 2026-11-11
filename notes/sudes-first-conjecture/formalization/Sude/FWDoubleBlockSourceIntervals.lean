import Sude.DoubleBlockScoreDecomposition
import Sude.FWPhysicalDoubleBlockCells
import Sude.FWBridgePairMidpointOfTheta
import Sude.FWWidePairMidpointOfTheta

/-! Same-square interval bounds for the existing grouped bridge and wide
source pair midpoints. No allocation, proxy, or placement existence is asserted. -/
namespace Sude
noncomputable section

/-- Source bridge pair midpoints lie in the narrow window about half the
pool maximum. This statement uses the actual supplied placement and does not
require theta or RS assumptions. -/
theorem fw_bridge_double_block_source_interval {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (initial : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (old : Cell n ≃ Fin (n * n))
    (hdiag : ∀ t side, entry old (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (hord : ∀ x, entry old (fwBridgeLayerCells rows cols hr hc x) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeOrdinarySlot n x))
    (j : Fin 5) (b : Fin (3 * (n + 8))) (p : Fin 2) :
    doubleBlockPairMidpoint (fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc) old j b p ∈
      Set.Icc ((poolMaximum n : ℝ) / 2 - (23 / 1848 : ℝ) * poolMaximum n)
        ((poolMaximum n : ℝ) / 2 + (23 / 1848 : ℝ) * poolMaximum n) := by
  have h := fw_bridge_selected_pair_midpoint_window hrect hs choice rows cols hr hc
    initial batches hvalid old hdiag hord j b p
  change |doubleBlockPairMidpoint (fwBridgePhysicalDoubleCells hrect hs choice rows cols hr hc) old j b p -
    (poolMaximum n : ℝ) / 2| ≤ (23 / 1848 : ℝ) * poolMaximum n at h
  exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩

/-- Source wide pair midpoints lie around the supplied mean, provided the
same old square places blocks valid in the specific reflected bins. -/
theorem fw_wide_double_block_source_interval {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (old : Cell n ≃ Fin (n * n))
    (hplaced : ∀ x : FWWideInputs n, entry old (fwWidePhysicalCells hwide hs choice rows cols hr hc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    (μ X : ℝ) (hX : 100 ≤ X)
    (hmlo : (243 / 500 : ℝ) * X ≤ μ) (hmhi : μ ≤ (123 / 250 : ℝ) * X)
    (hvalid : ∀ b ∈ blocks, b.MatchedValid
      (bmorLowBins (fwReflectedLeft μ X) (fwReflectedRight μ X))
      (bmorHighBins (fwReflectedLeft μ X) (fwReflectedRight μ X)))
    (j : Fin (3 * (n / 450))) (b : Fin (3 * (n + 8))) (p : Fin 2) :
    doubleBlockPairMidpoint (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc) old j b p ∈
      Set.Icc (μ - X / 235) (μ + X / 235) := by
  let q : Fin (6 * (n + 8)) :=
    Fin.cast (by omega : 3 * (n + 8) * 2 = 6 * (n + 8)) (finProdFinEquiv (b,p))
  have h := fw_wide_physical_pair_midpoint_bound hwide hs choice rows cols hr hc blocks hlen
    old hplaced μ X hX hmlo hmhi hvalid j q
  change |doubleBlockPairMidpoint (fwWidePhysicalDoubleCells hwide hs choice rows cols hr hc) old j b p - μ| ≤ X / 235 at h
  exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩

end
end Sude
