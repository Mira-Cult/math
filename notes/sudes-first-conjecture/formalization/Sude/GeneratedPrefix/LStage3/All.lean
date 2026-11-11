import Sude.GeneratedPrefix.LStage3.B451

/-! Checked stage-3 prefix. Full acceptance requires all 452 blocks. -/
namespace Sude.GeneratedPrefix.LStage3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev lows : List ℕ := B451.accumulated

theorem length : lows.length = 14448 := B451.prefix_length

theorem valid : PrefixStageBlock 16 55000000 23744473 26908477 lows := B451.prefix_valid

theorem pool_matching (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) :
    (∀ p ∈ lows.toFinset, p ∈ pool n ∧ p + 16 ∈ pool n) ∧
      PairwiseDisjointPairs lows.toFinset 16 ∧
      (pairFootprint lows.toFinset 16).card = 2 * 14448 := by
  have h := PrefixStageBlock.L_pool_matching (j := 3) lower hn (by decide) B451.prefix_valid
  simpa [lows, length] using h

end Sude.GeneratedPrefix.LStage3
