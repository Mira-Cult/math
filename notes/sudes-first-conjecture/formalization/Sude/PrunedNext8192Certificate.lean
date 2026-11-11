import Sude.PrunedFirst8192Certificate

/-! Second half of the additional prefix, separately kernel checked. -/
namespace Sude
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem prunedNext8192_checked :
    prunedSegmentScan (canonicalPrimeBaseList 257) 49155 pruned8192Widths =
      (1492, 85405292) := by
  decide +kernel

end
end Sude
