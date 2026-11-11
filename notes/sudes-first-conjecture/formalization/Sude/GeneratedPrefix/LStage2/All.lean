import Sude.GeneratedPrefix.LStage2.B451

/-! Checked stage-2 prefix. Full acceptance requires all 452 blocks. -/
namespace Sude.GeneratedPrefix.LStage2
set_option maxRecDepth 100000
set_option maxHeartbeats 0

abbrev lows : List ℕ := B451.accumulated

theorem length : lows.length = 14448 := B451.prefix_length

theorem valid : PrefixStageBlock 8 55000000 20288483 23379269 lows := B451.prefix_valid

theorem pool_matching (lower : RSIndexLower) {n : ℕ} (hn : 2000 ≤ n) :
    (∀ p ∈ lows.toFinset, p ∈ pool n ∧ p + 8 ∈ pool n) ∧
      PairwiseDisjointPairs lows.toFinset 8 ∧
      (pairFootprint lows.toFinset 8).card = 2 * 14448 := by
  have h := PrefixStageBlock.L_pool_matching (j := 2) lower hn (by decide) B451.prefix_valid
  simpa [lows, length] using h

end Sude.GeneratedPrefix.LStage2
