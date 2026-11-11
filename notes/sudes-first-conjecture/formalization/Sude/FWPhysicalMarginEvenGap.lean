import Sude.FWPhysicalMarginStock
import Sude.FWInstalledGap

/-! Retain positive even source-sized gaps in FW's physical supply witness. -/
namespace Sude
noncomputable section

/-- Under the unchanged margin-supply hypotheses, the very same installed
blocks have a positive even shared gap in `[2X/3, X)` for every block.
The mean, real margin, budget, physical cells and later controller work
remain explicit obligations. -/
theorem fw_reflected_supply_with_margin_and_even_gaps {n B k : ℕ}
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
        (fun x => cells (Fin.cast hlen x.1, x.2)) ∧
      (∀ i : Fin blocks.length, ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
        entry a' (cells (Fin.cast hlen i, 1)) = entry a' (cells (Fin.cast hlen i, 0)) + gap ∧
        entry a' (cells (Fin.cast hlen i, 2)) = entry a' (cells (Fin.cast hlen i, 3)) + gap ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n) := by
  have hXnat : 100 ≤ poolMaximum n :=
    (by decide : 100 ≤ 4 * 2 ^ 30).trans (le_of_lt (fw_poolMaximum_gt_four_seed lower hnlo))
  have hX : (100 : ℝ) ≤ poolMaximum n := by exact_mod_cast hXnat
  obtain ⟨blocks, hlen, a', hmatched, hpair, havoid, hplace, hfixed, hbounds⟩ :=
    fw_reflected_supply_with_floored_stock_of_margin bmor upper lower hnlo hnhi m hmlo hmhi
      removed hmargin hbudget a cells reserved hcells hnew hreserved
  refine ⟨blocks, hlen, a', hmatched, hpair, havoid, hplace, hfixed, hbounds, ?_⟩
  intro i
  exact fw_installed_matched_block_even_gap m (poolMaximum n) hX hmlo hmhi blocks a'
    (fun x => cells (Fin.cast hlen x.1, x.2)) hmatched hplace i

end
end Sude
