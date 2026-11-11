import Sude.FWPhysicalMarginEvenGap
import Sude.FWEarlyBudgetSharp

/-! FW physical supply using an explicit sharp published prime-index bound. -/
namespace Sude
noncomputable section

/-- The sharp RS index premise and the fixed FW10 budget supply the stock
margin. Actual deletion accounting, the mean, cell geometry and subsequent
controller steps remain explicit obligations. -/
theorem fw_reflected_supply_with_sharp_early_budget_and_even_gaps {n k : ℕ}
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp)
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (m : ℝ)
    (hmlo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤ m)
    (hmhi : m ≤ (123 / 250 : ℝ) * (poolMaximum n : ℝ))
    (removed : Finset ℕ)
    (hbudget : removed.card + 4 * k ≤ fwEarlyBudget n)
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
        (fun x => cells (Fin.cast hlen x.1, x.2)) ∧
      (∀ i : Fin blocks.length, ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
        entry a' (cells (Fin.cast hlen i, 1)) = entry a' (cells (Fin.cast hlen i, 0)) + gap ∧
        entry a' (cells (Fin.cast hlen i, 2)) = entry a' (cells (Fin.cast hlen i, 3)) + gap ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n) := by
  have hmargin := fw_early_budget_real_margin_of_sharp_index upper lower sharp hnlo hnhi
  exact fw_reflected_supply_with_margin_and_even_gaps bmor upper lower hnlo hnhi m hmlo hmhi
    removed hmargin hbudget a cells reserved hcells hnew hreserved

end
end Sude
