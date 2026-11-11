import Sude.PrunedNext8192Certificate
import Sude.StreamingPrefix16384

/-! Separately accepted blocks compose with the earlier prime prefix. -/
namespace Sude
noncomputable section

theorem prunedFirst8192_prime_count_sum :
    (oddPrimeSegment 32771 49155).card = 1539 ∧
      (∑ p ∈ oddPrimeSegment 32771 49155, p) = 62891569 := by
  have hbit : bitsetSegmentScan (canonicalPrimeBaseList 257) 32771 pruned8192Widths =
      (1539, 62891569) :=
    (streamingSegmentScan_eq (canonicalPrimeBaseList 257) 32771 pruned8192Widths).symm.trans
      ((prunedSegmentScan_eq (canonicalPrimeBaseList 257) 32771 pruned8192Widths
        (by decide)).symm.trans prunedFirst8192_checked)
  have h := bitsetScan_count_sum (canonicalPrimeBaseList 257) 257 32771
    pruned8192Widths 1539 62891569 (canonicalPrimeBaseList_complete 257)
    (by decide) (by decide) (by rw [pruned8192Widths_sum]; decide) hbit
  simpa only [pruned8192Widths_sum, show 32771 + 2 * 8192 = 49155 by decide] using h

theorem prunedNext8192_prime_count_sum :
    (oddPrimeSegment 49155 65539).card = 1492 ∧
      (∑ p ∈ oddPrimeSegment 49155 65539, p) = 85405292 := by
  have hbit : bitsetSegmentScan (canonicalPrimeBaseList 257) 49155 pruned8192Widths =
      (1492, 85405292) :=
    (streamingSegmentScan_eq (canonicalPrimeBaseList 257) 49155 pruned8192Widths).symm.trans
      ((prunedSegmentScan_eq (canonicalPrimeBaseList 257) 49155 pruned8192Widths
        (by decide)).symm.trans prunedNext8192_checked)
  have h := bitsetScan_count_sum (canonicalPrimeBaseList 257) 257 49155
    pruned8192Widths 1492 85405292 (canonicalPrimeBaseList_complete 257)
    (by decide) (by decide) (by rw [pruned8192Widths_sum]; decide) hbit
  simpa only [pruned8192Widths_sum, show 49155 + 2 * 8192 = 65539 by decide] using h

/-- The first 32,768 odd candidates are covered by accepted scans. -/
theorem prunedFirst32768_prime_count_sum :
    (oddPrimeSegment 3 65539).card = 6542 ∧
      (∑ p ∈ oddPrimeSegment 3 65539, p) = 202353622 := by
  have hnext := combineOddPrimeSegments (lo := 32771) (mid := 49155) (hi := 65539)
    (by decide) (by decide) prunedFirst8192_prime_count_sum prunedNext8192_prime_count_sum
  have h := combineOddPrimeSegments (lo := 3) (mid := 32771) (hi := 65539)
    (by decide) (by decide) streamingFirst16384_prime_count_sum hnext
  change (oddPrimeSegment 3 65539).card = 6542 ∧
    (∑ p ∈ oddPrimeSegment 3 65539, p) = 202353622 at h
  exact h

end
end Sude
