import Sude.SegmentedScan

/-! A second independently kernel-checked block of the needed prime prefix.
The interval between this and the initial block remains unverified. -/
namespace Sude
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def latePrefixWidths : List ℕ := List.replicate 32 16

theorem latePrefixWidths_sum : latePrefixWidths.sum = 512 := by decide +kernel

theorem latePrefixScan_checked :
    markingSegmentScan (canonicalPrimeBase 90) 7171 latePrefixWidths = (112, 859924) := by
  decide +kernel

theorem latePrefixPrimeSegment_count_sum :
    (oddPrimeSegment 7171 8195).card = 112 ∧
      (∑ p ∈ oddPrimeSegment 7171 8195, p) = 859924 := by
  have hs := markingSegmentScan_spec (canonicalPrimeBase 90) 90 7171 latePrefixWidths
    (canonicalPrimeBase_complete 90) (by decide) (by decide) (by rw [latePrefixWidths_sum]; decide)
  rw [latePrefixScan_checked, latePrefixWidths_sum] at hs
  have heq : (112, 859924) =
      ((oddPrimeSegment 7171 8195).card, ∑ p ∈ oddPrimeSegment 7171 8195, p) := by
    simpa only [show 7171 + 2 * 512 = 8195 by decide] using hs
  exact ⟨(congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm⟩

end
end Sude
