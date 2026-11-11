import Sude.PrunedBitset

/-! First half of the additional prefix, separately kernel checked. -/
namespace Sude
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def pruned8192Widths : List ℕ := List.replicate 8 1024

theorem pruned8192Widths_sum : pruned8192Widths.sum = 8192 := by decide +kernel

theorem prunedFirst8192_checked :
    prunedSegmentScan (canonicalPrimeBaseList 257) 32771 pruned8192Widths =
      (1539, 62891569) := by
  decide +kernel

end
end Sude
