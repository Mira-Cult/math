import Sude.BitsetSieve

/-! Kernel evaluation of the first 4,096 odd candidates using bitset marks.
The remaining tail prefix and all controller obligations remain open. -/
namespace Sude
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bitsetFirst4096Widths : List ℕ := List.replicate 64 64

theorem bitsetFirst4096Widths_sum : bitsetFirst4096Widths.sum = 4096 := by
  decide +kernel

/-- Actual kernel reduction of all 64 bitset-marked segments. -/
theorem bitsetFirst4096_checked :
    bitsetSegmentScan (canonicalPrimeBaseList 90) 3 bitsetFirst4096Widths = (1027, 3908639) := by
  decide +kernel

/-- The accepted scan proves the count and sum for the mathematical segment. -/
theorem bitsetFirst4096_prime_count_sum :
    (oddPrimeSegment 3 8195).card = 1027 ∧
      (∑ p ∈ oddPrimeSegment 3 8195, p) = 3908639 := by
  have h := markingSegmentScan_spec (canonicalPrimeBaseList 90).toFinset 90 3
    bitsetFirst4096Widths (canonicalPrimeBaseList_complete 90) (by decide) (by decide)
    (by rw [bitsetFirst4096Widths_sum]; decide)
  rw [← bitsetSegmentScan_eq, bitsetFirst4096_checked, bitsetFirst4096Widths_sum] at h
  have heq : (1027, 3908639) =
      ((oddPrimeSegment 3 8195).card, ∑ p ∈ oddPrimeSegment 3 8195, p) := by
    simpa only [show 3 + 2 * 4096 = 8195 by decide] using h
  exact ⟨(congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm⟩

end
end Sude
