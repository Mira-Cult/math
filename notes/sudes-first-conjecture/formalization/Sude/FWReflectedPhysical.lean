import Sude.FWReflectedGeometry
import Sude.BMORPhysicalMatchedBlocks

/-! Compose FW's exact reflected geometry with physical BMOR block supply. -/
namespace Sude
noncomputable section

/-- Under the explicit FW mean, stock and square-gate hypotheses, the
published BMOR and RS inputs provide equal-gap blocks from FW's actual
reflected bins and install them into supplied distinct cells while keeping
reserved cells fixed. The internal mean, numerical gates, capacity and the
remaining controller are not proved here. -/
theorem fw_reflected_select_and_install {n W B k : ℕ}
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
      (∀ block ∈ blocks, block.valid (Finset.univ.biUnion low) (Finset.univ.biUnion high)) ∧
      blocks.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ block ∈ blocks, Disjoint block.footprint removed) ∧
      (∀ x : Fin blocks.length × Fin 4,
        entry a' (cells (Fin.cast hlen x.1, x.2)) = doublePairSequenceEndpoint blocks x) ∧
      (∀ cell ∈ reserved, entry a' cell = entry a cell) := by
  have hXnat : 100 ≤ poolMaximum n :=
    (by decide : 100 ≤ 4 * 2 ^ 30).trans (le_of_lt (fw_poolMaximum_gt_four_seed lower hnlo))
  have hX : (100 : ℝ) ≤ poolMaximum n := by exact_mod_cast hXnat
  obtain ⟨hends, hsep, hcross, _⟩ := fw_reflected_bin_geometry m (poolMaximum n) hX hmlo hmhi
  exact bmor_select_and_install_matched_blocks bmor upper _ _ (by omega) (by omega)
    (fun z => (hends z).1) (fun z => (hends z).2.1) (fun z => (hends z).2.2)
    hsep hcross hW removed hgate hbudget a cells reserved hcells hnew hreserved

end
end Sude
