import Sude.BMORMatchedBinInputs
import Sude.MatchedBinPhysicalPlacement

/-! Compose the published BMOR input with physical matched-block placement. -/
namespace Sude
noncomputable section

/-- From the published finite BMOR and RS inputs and explicit interval,
stock, budget, gate and cell hypotheses, select and physically install a
batch of disjoint equal-gap blocks drawn from the exact prescribed pool.
The source-specific numerical premises and the remainder of the controller
are not assumed or proved by this theorem. -/
theorem bmor_select_and_install_matched_blocks {n N W B k : ℕ}
    (h : BMORFiniteTheta) (upper : RSIndexUpper) (b c : Fin N × Bool → ℝ)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hb : ∀ z, 1 ≤ b z) (hbc : ∀ z, b z ≤ c z)
    (hcX : ∀ z, c z ≤ (poolMaximum n : ℝ))
    (hsep : ∀ z t, z ≠ t → c z ≤ b t ∨ c t ≤ b z)
    (hcross : ∀ i j, c (i, false) ≤ b (j, true))
    (hW : ∀ z, (W : ℝ) ≤
      ((c z - b z) - (518 / 125 : ℝ) * (Real.sqrt (b z) + Real.sqrt (c z))) /
        Real.log (poolMaximum n : ℝ))
    (removed : Finset ℕ)
    (hgate : (N : ℝ) * (poolMaximum n : ℝ) < ((N * W - B : ℕ) : ℝ) ^ 2)
    (hbudget : removed.card + 4 * k ≤ B)
    (a : Cell n ≃ Fin (n * n)) (cells : Fin k × Fin 4 → Cell n)
    (reserved : Finset (Cell n)) (hcells : Function.Injective cells)
    (hnew : ∀ x, cells x ∉ reserved)
    (hreserved : ∀ c ∈ reserved, entry a c ∈ removed) :
    let low := bmorLowBins b c
    let high := bmorHighBins b c
    ∃ (blocks : List DoublePair) (hlen : blocks.length = k) (a' : Cell n ≃ Fin (n * n)),
      (∀ block ∈ blocks, block.valid (Finset.univ.biUnion low) (Finset.univ.biUnion high)) ∧
      blocks.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ block ∈ blocks, Disjoint block.footprint removed) ∧
      (∀ x : Fin blocks.length × Fin 4,
        entry a' (cells (Fin.cast hlen x.1, x.2)) = doublePairSequenceEndpoint blocks x) ∧
      (∀ cell ∈ reserved, entry a' cell = entry a cell) := by
  classical
  dsimp only
  obtain ⟨hdis, hlow, hhigh, horder, hdiff, hpoolL, hpoolH⟩ :=
    bmor_two_matched_bin_inputs h upper n W b c hn hnmax hb hbc hcX hsep hcross hW
  exact select_and_install_matched_bin_blocks (bmorLowBins b c) (bmorHighBins b c)
    removed (Finset.range (poolMaximum n)) hdis hlow hhigh horder hdiff
    (by simp) hgate hbudget hpoolL hpoolH a cells reserved hcells hnew hreserved

end
end Sude
