import Sude.FWReflectedPhysicalPreserved
import Sude.FWInstalledBlockGeometry

/-! Pair geometry for the actual FW physical placement. -/
namespace Sude
noncomputable section

/-- Both physically installed pairs of each block satisfy the FW
midpoint and gap bounds. -/
def fwInstalledPairBounds {n : ℕ} (m X : ℝ) (blocks : List DoublePair)
    (a : Cell n ≃ Fin (n * n)) (cells : Fin blocks.length × Fin 4 → Cell n) : Prop :=
  ∀ i : Fin blocks.length,
    |((entry a (cells (i, 0)) : ℝ) + entry a (cells (i, 1))) / 2 - m| ≤ X / 235 ∧
      (2 / 3 : ℝ) * X ≤ (entry a (cells (i, 1)) : ℝ) - entry a (cells (i, 0)) ∧
      (entry a (cells (i, 1)) : ℝ) - entry a (cells (i, 0)) ≤
        (2 * ((16 / 235 : ℝ) + 1 / 3) + 2 * (16 / 235 : ℝ)) * X ∧
    |((entry a (cells (i, 3)) : ℝ) + entry a (cells (i, 2))) / 2 - m| ≤ X / 235 ∧
      (2 / 3 : ℝ) * X ≤ (entry a (cells (i, 2)) : ℝ) - entry a (cells (i, 3)) ∧
      (entry a (cells (i, 2)) : ℝ) - entry a (cells (i, 3)) ≤
        (2 * ((16 / 235 : ℝ) + 1 / 3) + 2 * (16 / 235 : ℝ)) * X

/-- Under explicit FW mean, stock, numerical-gate and physical-cell
hypotheses, install source-matched blocks whose actual physical pairs meet
the FW midpoint and gap bounds. These hypotheses and the later controller
steps remain open internal obligations. -/
theorem fw_reflected_select_install_with_pair_bounds {n W B k : ℕ}
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (m : ℝ)
    (hmlo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤ m)
    (hmhi : m ≤ (123 / 250 : ℝ) * (poolMaximum n : ℝ))
    (hW : ∀ z, (W : ℝ) ≤
      ((fwReflectedRight m (poolMaximum n) z - fwReflectedLeft m (poolMaximum n) z) -
        (518 / 125 : ℝ) * (Real.sqrt (fwReflectedLeft m (poolMaximum n) z) +
          Real.sqrt (fwReflectedRight m (poolMaximum n) z))) /
        Real.log (poolMaximum n : ℝ))
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
  obtain ⟨blocks, hlen, a', hmatched, hpair, havoid, hplace, hfixed⟩ :=
    fw_reflected_select_and_install_preserving_labels bmor upper lower hnlo hnhi m hmlo hmhi
      hW removed hgate hbudget a cells reserved hcells hnew hreserved
  have hbounds : fwInstalledPairBounds m (poolMaximum n) blocks a'
      (fun x => cells (Fin.cast hlen x.1, x.2)) := by
    intro i
    exact fw_installed_matched_block_bounds m (poolMaximum n) hX hmlo hmhi blocks a'
      (fun x => cells (Fin.cast hlen x.1, x.2)) hmatched hplace i
  exact ⟨blocks, hlen, a', hmatched, hpair, havoid, hplace, hfixed, hbounds⟩

end
end Sude
