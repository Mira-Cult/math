import Sude.SegmentedScan

/-! A kernel-evaluated initial block of the prime prefix. This does not
establish the much longer prefix required at the first tail order. -/
namespace Sude
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def firstPrefixWidths : List ℕ := List.replicate 8 16

theorem firstPrefixWidths_sum : firstPrefixWidths.sum = 128 := by decide +kernel

/-- The eight concrete marking segments are evaluated by kernel reduction. -/
theorem firstPrefixScan_checked :
    markingSegmentScan (canonicalPrimeBase 16) 3 firstPrefixWidths = (54, 6336) := by
  decide +kernel

/-- The accepted count and sum are the mathematical odd-prime segment,
not just an unchecked output of the scan. -/
theorem firstPrefixPrimeSegment_count_sum :
    (oddPrimeSegment 3 259).card = 54 ∧
      (∑ p ∈ oddPrimeSegment 3 259, p) = 6336 := by
  have hs := markingSegmentScan_spec (canonicalPrimeBase 16) 16 3 firstPrefixWidths
    (canonicalPrimeBase_complete 16) (by decide) (by decide) (by rw [firstPrefixWidths_sum]; decide)
  rw [firstPrefixScan_checked, firstPrefixWidths_sum] at hs
  have heq : (54, 6336) =
      ((oddPrimeSegment 3 259).card, ∑ p ∈ oddPrimeSegment 3 259, p) := by
    simpa only [show 3 + 2 * 128 = 259 by decide] using hs
  exact ⟨(congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm⟩

/-- A larger contiguous block: 32 segments of 16 odd candidates. -/
def first512Widths : List ℕ := List.replicate 32 16

theorem first512Widths_sum : first512Widths.sum = 512 := by decide +kernel

theorem first512Scan_checked :
    markingSegmentScan (canonicalPrimeBase 32) 3 first512Widths = (171, 80187) := by
  decide +kernel

theorem first512PrimeSegment_count_sum :
    (oddPrimeSegment 3 1027).card = 171 ∧
      (∑ p ∈ oddPrimeSegment 3 1027, p) = 80187 := by
  have hs := markingSegmentScan_spec (canonicalPrimeBase 32) 32 3 first512Widths
    (canonicalPrimeBase_complete 32) (by decide) (by decide) (by rw [first512Widths_sum]; decide)
  rw [first512Scan_checked, first512Widths_sum] at hs
  have heq : (171, 80187) =
      ((oddPrimeSegment 3 1027).card, ∑ p ∈ oddPrimeSegment 3 1027, p) := by
    simpa only [show 3 + 2 * 512 = 1027 by decide] using hs
  exact ⟨(congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm⟩

end
end Sude
