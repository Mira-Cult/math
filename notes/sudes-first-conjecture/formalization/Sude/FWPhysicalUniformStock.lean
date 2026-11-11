import Sude.FWPhysicalSupplyWithGeometry
import Sude.FWReflectedStockGate

/-! One source-style stock gate for the full FW physical supply. -/
namespace Sude
noncomputable section

/-- The FW physical supply with actual installed-pair bounds follows from
one explicit midpoint-error stock gate. The mean, scalar stock gate, square
gate, cell hypotheses and subsequent controller steps remain open. -/
theorem fw_reflected_supply_with_uniform_stock_gate {n W B k : ℕ}
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (m : ℝ)
    (hmlo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤ m)
    (hmhi : m ≤ (123 / 250 : ℝ) * (poolMaximum n : ℝ))
    (hW : (W : ℝ) ≤
      ((2 / 235 : ℝ) * (poolMaximum n : ℝ) - 2 * (518 / 125 : ℝ) *
        Real.sqrt (((123 / 250 : ℝ) + ((16 / 235 : ℝ) + 1 / 3) + 16 / 235) *
          (poolMaximum n : ℝ))) / Real.log (poolMaximum n : ℝ))
    (removed : Finset ℕ)
    (hgate : (16 : ℝ) * (poolMaximum n : ℝ) < ((16 * W - B : ℕ) : ℝ) ^ 2)
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
  have hXnat : 100 ≤ poolMaximum n :=
    (by decide : 100 ≤ 4 * 2 ^ 30).trans (le_of_lt (fw_poolMaximum_gt_four_seed lower hnlo))
  have hX : (100 : ℝ) ≤ poolMaximum n := by exact_mod_cast hXnat
  have hW' := fw_reflected_uniform_endpoint_gate m (poolMaximum n) W hX hmlo hmhi hW
  exact fw_reflected_select_install_with_pair_bounds bmor upper lower hnlo hnhi m hmlo hmhi
    hW' removed hgate hbudget a cells reserved hcells hnew hreserved

end
end Sude
