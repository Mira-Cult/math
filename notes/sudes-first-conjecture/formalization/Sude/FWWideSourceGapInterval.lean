import Sude.FWPermutedWideGapBounds

/-! The actual matched-wide source block gaps lie in one common interval.
This statement does not select a permutation or assert any square property. -/
namespace Sude
noncomputable section

/-- Each source gap has width at most `(64/235) * X` above the common
lower endpoint. The source block and its order come from the same supplied
matched list. -/
theorem fw_wide_source_gap_interval {n : ℕ}
    (μ X : ℝ) (hX : (100 : ℝ) ≤ X)
    (hmlo : (243/500 : ℝ)*X ≤ μ) (hmhi : μ ≤ (123/250 : ℝ)*X)
    (blocks : List DoublePair)
    (hlen : blocks.length = (3*(n/450))*(3*(n+8)))
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft μ X) (fwReflectedRight μ X))
      (bmorHighBins (fwReflectedLeft μ X) (fwReflectedRight μ X)))
    (j : Fin (3*(n/450))) (b : Fin (3*(n+8))) :
    (fwPermutedWideSourceGap blocks hlen (fun _ => Equiv.refl _) j b : ℝ) ∈
      Set.Icc ((2/3 : ℝ)*X) (((2/3 : ℝ)+(64/235 : ℝ))*X) := by
  let idx := Fin.cast hlen.symm (finProdFinEquiv (j,b))
  let block := blocks.get idx
  have hm : block.MatchedValid
      (bmorLowBins (fwReflectedLeft μ X) (fwReflectedRight μ X))
      (bmorHighBins (fwReflectedLeft μ X) (fwReflectedRight μ X)) :=
    hmatched block (List.get_mem blocks idx)
  have hg := fw_matched_block_pair_bounds μ X hX hmlo hmhi block hm
  have hord : block.low₁ ≤ block.high₁ := by
    rcases hm.1 with ⟨_, _, _, _, _, _, horder, _, _⟩
    exact Nat.le_of_lt horder
  have hcast : ((block.high₁ - block.low₁ : ℕ) : ℝ) =
      (block.high₁ : ℝ) - (block.low₁ : ℝ) := Nat.cast_sub hord
  change ((block.high₁ - block.low₁ : ℕ) : ℝ) ∈ _
  rw [hcast]
  constructor
  · exact hg.2.1
  · have hu := hg.2.2.1
    norm_num at hu ⊢
    linarith

end
end Sude
