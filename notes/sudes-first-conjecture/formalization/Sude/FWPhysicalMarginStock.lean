import Sude.FWPhysicalFloorStock
import Sude.FWStockRoundingGate

/-! Replace the floored square gate by an explicitly supplied real margin. -/
namespace Sude
noncomputable section

/-- The same physical conclusion follows from the floor-safe real margin.
The margin and all other FW construction hypotheses remain obligations. -/
theorem fw_reflected_supply_with_floored_stock_of_margin {n B k : ℕ}
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (m : ℝ)
    (hmlo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤ m)
    (hmhi : m ≤ (123 / 250 : ℝ) * (poolMaximum n : ℝ))
    (removed : Finset ℕ)
    (hmargin : (B : ℝ) + 16 + 4 * Real.sqrt (poolMaximum n : ℝ) ≤
      16 * fwUniformRealStock (poolMaximum n : ℝ))
    (hbudget : removed.card + 4 * k ≤ B)
    (a : Cell n ≃ Fin (n * n)) (cells : Fin k × Fin 4 → Cell n)
    (reserved : Finset (Cell n)) (hcells : Function.Injective cells)
    (hnew : ∀ x, cells x ∉ reserved)
    (hreserved : ∀ c ∈ reserved, entry a c ∈ removed) :
    let low := bmorLowBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    let high := bmorHighBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    ∃ (blocks : List DoublePair) (hlen : blocks.length = k) (a' : Cell n ≃ Fin (n * n)),
      (∀ block ∈ blocks, block.MatchedValid low high) ∧
      blocks.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ block ∈ blocks, Disjoint block.footprint removed) ∧
      (∀ x : Fin blocks.length × Fin 4,
        entry a' (cells (Fin.cast hlen x.1, x.2)) = doublePairSequenceEndpoint blocks x) ∧
      (∀ cell ∈ reserved, entry a' cell = entry a cell) ∧
      fwInstalledPairBounds m (poolMaximum n) blocks a'
        (fun x => cells (Fin.cast hlen x.1, x.2)) := by
  have hX : (0 : ℝ) ≤ poolMaximum n := by exact_mod_cast (Nat.zero_le (poolMaximum n))
  have hgate := fw_uniform_floored_stock_square_gate (poolMaximum n : ℝ) B hX hmargin
  exact fw_reflected_supply_with_floored_stock bmor upper lower hnlo hnhi m hmlo hmhi
    removed hgate hbudget a cells reserved hcells hnew hreserved

end
end Sude
