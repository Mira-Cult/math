import Sude.FWMatchedBlockGeometry
import Sude.DoublePairPlacement

/-! Transfer FW matched-pair geometry to the installed physical entries. -/
namespace Sude
noncomputable section

/-- Each installed label-preserving FW block has both actual physical pairs
inside the source midpoint and gap ranges. The caller supplies the exact
placement and the internal mean interval. -/
theorem fw_installed_matched_block_bounds {n : ℕ}
    (m X : ℝ) (hX : 100 ≤ X)
    (hmlo : (243 / 500 : ℝ) * X ≤ m) (hmhi : m ≤ (123 / 250 : ℝ) * X)
    (blocks : List DoublePair) (a : Cell n ≃ Fin (n * n))
    (cells : Fin blocks.length × Fin 4 → Cell n)
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft m X) (fwReflectedRight m X))
      (bmorHighBins (fwReflectedLeft m X) (fwReflectedRight m X)))
    (hplaced : ∀ x, entry a (cells x) = doublePairSequenceEndpoint blocks x)
    (i : Fin blocks.length) :
    |((entry a (cells (i, 0)) : ℝ) + entry a (cells (i, 1))) / 2 - m| ≤ X / 235 ∧
      (2 / 3 : ℝ) * X ≤ (entry a (cells (i, 1)) : ℝ) - entry a (cells (i, 0)) ∧
      (entry a (cells (i, 1)) : ℝ) - entry a (cells (i, 0)) ≤
        (2 * ((16 / 235 : ℝ) + 1 / 3) + 2 * (16 / 235 : ℝ)) * X ∧
    |((entry a (cells (i, 3)) : ℝ) + entry a (cells (i, 2))) / 2 - m| ≤ X / 235 ∧
      (2 / 3 : ℝ) * X ≤ (entry a (cells (i, 2)) : ℝ) - entry a (cells (i, 3)) ∧
      (entry a (cells (i, 2)) : ℝ) - entry a (cells (i, 3)) ≤
        (2 * ((16 / 235 : ℝ) + 1 / 3) + 2 * (16 / 235 : ℝ)) * X := by
  have h0 : entry a (cells (i, 0)) = (blocks.get i).low₁ := by rw [hplaced]; rfl
  have h1 : entry a (cells (i, 1)) = (blocks.get i).high₁ := by rw [hplaced]; rfl
  have h2 : entry a (cells (i, 2)) = (blocks.get i).high₂ := by rw [hplaced]; rfl
  have h3 : entry a (cells (i, 3)) = (blocks.get i).low₂ := by rw [hplaced]; rfl
  rw [h0, h1, h2, h3]
  exact fw_matched_block_pair_bounds m X hX hmlo hmhi (blocks.get i)
    (hmatched (blocks.get i) (List.get_mem blocks i))

end
end Sude
