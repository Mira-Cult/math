import Sude.BitsetNext4096Certificate
import Sude.SegmentResults

/-! A second independently checked bitset block, composed with the first. -/
namespace Sude
noncomputable section

theorem bitsetNext4096_prime_count_sum :
    (oddPrimeSegment 8195 16387).card = 872 ∧
      (∑ p ∈ oddPrimeSegment 8195 16387, p) = 10676000 := by
  have h := bitsetScan_count_sum (canonicalPrimeBaseList 128) 128 8195
    bitsetFirst4096Widths 872 10676000 (canonicalPrimeBaseList_complete 128)
    (by decide) (by decide) (by rw [bitsetFirst4096Widths_sum]; decide)
    bitsetNext4096_checked
  simpa only [bitsetFirst4096Widths_sum, show 8195 + 2 * 4096 = 16387 by decide] using h

/-- The two separately accepted blocks cover the first 8,192 candidates. -/
theorem bitsetFirst8192_prime_count_sum :
    (oddPrimeSegment 3 16387).card = 1899 ∧
      (∑ p ∈ oddPrimeSegment 3 16387, p) = 14584639 := by
  have h := combineOddPrimeSegments (lo := 3) (mid := 8195) (hi := 16387)
    (by decide) (by decide) bitsetFirst4096_prime_count_sum bitsetNext4096_prime_count_sum
  change (oddPrimeSegment 3 16387).card = 1899 ∧
    (∑ p ∈ oddPrimeSegment 3 16387, p) = 14584639 at h
  exact h

end
end Sude
