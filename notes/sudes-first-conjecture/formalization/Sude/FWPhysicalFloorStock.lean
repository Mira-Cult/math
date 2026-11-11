import Sude.FWPhysicalUniformStock
import Sude.FWUniformStockFloor

/-! Fix the FW bin stock as the floor of the proved BMOR lower bound. -/
namespace Sude
noncomputable section

/-- The physical FW wide-block supply uses a concrete rounded stock and
requires no independent stock lower-bound hypothesis. The mean interval,
rounded square gate, budget, cell hypotheses and the rest of FW remain open. -/
theorem fw_reflected_supply_with_floored_stock {n B k : ℕ}
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (m : ℝ)
    (hmlo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤ m)
    (hmhi : m ≤ (123 / 250 : ℝ) * (poolMaximum n : ℝ))
    (removed : Finset ℕ)
    (hgate : (16 : ℝ) * (poolMaximum n : ℝ) < ((16 * fwUniformNaturalStock (poolMaximum n) - B : ℕ) : ℝ) ^ 2)
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
  have hXnat : 100000000 ≤ poolMaximum n :=
    (by decide : 100000000 ≤ 4 * 2 ^ 30).trans (le_of_lt (fw_poolMaximum_gt_four_seed lower hnlo))
  have hX : (100000000 : ℝ) ≤ poolMaximum n := by exact_mod_cast hXnat
  have hW := fw_uniform_natural_stock_le (poolMaximum n) hX
  exact fw_reflected_supply_with_uniform_stock_gate bmor upper lower hnlo hnhi m hmlo hmhi
    hW removed hgate hbudget a cells reserved hcells hnew hreserved

end
end Sude
