import Sude.StreamingBitset
import Sude.SegmentResults

/-! Kernel-checked larger initial block of the tail's prime prefix. -/
namespace Sude
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def streamingFirst16384Widths : List ℕ := List.replicate 16 1024

theorem streamingFirst16384Widths_sum : streamingFirst16384Widths.sum = 16384 := by
  decide +kernel

/-- Sixteen actual streamed bitset segments, checked by kernel reduction. -/
theorem streamingFirst16384_checked :
    streamingSegmentScan (canonicalPrimeBaseList 181) 3 streamingFirst16384Widths = (3511, 54056761) := by
  decide +kernel

theorem streamingFirst16384_prime_count_sum :
    (oddPrimeSegment 3 32771).card = 3511 ∧
      (∑ p ∈ oddPrimeSegment 3 32771, p) = 54056761 := by
  have hbit : bitsetSegmentScan (canonicalPrimeBaseList 181) 3 streamingFirst16384Widths =
      (3511, 54056761) :=
    (streamingSegmentScan_eq (canonicalPrimeBaseList 181) 3 streamingFirst16384Widths).symm.trans
      streamingFirst16384_checked
  have h := bitsetScan_count_sum (canonicalPrimeBaseList 181) 181 3
    streamingFirst16384Widths 3511 54056761 (canonicalPrimeBaseList_complete 181)
    (by decide) (by decide) (by rw [streamingFirst16384Widths_sum]; decide) hbit
  simpa only [streamingFirst16384Widths_sum, show 3 + 2 * 16384 = 32771 by decide] using h

end
end Sude
