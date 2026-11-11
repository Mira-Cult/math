import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B81 (S324..S327). -/
namespace Sude.FastTwinScan
namespace B81
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 679477293 681574445 = 6703 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 679477293 681574445).card = 6703 := by
  have h := fastStrideSixIntervalScan_spec 679477293 681574445 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 681574445 683671597 = 6678 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 681574445 683671597).card = 6678 := by
  have h := fastStrideSixIntervalScan_spec 681574445 683671597 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 683671597 685768749 = 6750 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 683671597 685768749).card = 6750 := by
  have h := fastStrideSixIntervalScan_spec 683671597 685768749 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 685768749 687865901 = 6703 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 685768749 687865901).card = 6703 := by
  have h := fastStrideSixIntervalScan_spec 685768749 687865901 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 679477293 683671597).card = 13381 := by
  simpa using combineTwinPrimeSegments (by decide : 679477293 ≤ 681574445) (by decide : 681574445 ≤ 683671597) seg0 seg1

theorem join23 : (twinPrimeSegment 683671597 687865901).card = 13453 := by
  simpa using combineTwinPrimeSegments (by decide : 683671597 ≤ 685768749) (by decide : 685768749 ≤ 687865901) seg2 seg3

theorem total : (twinPrimeSegment 679477293 687865901).card = 26834 := by
  simpa using combineTwinPrimeSegments (by decide : 679477293 ≤ 683671597) (by decide : 683671597 ≤ 687865901) join01 join23

end
end B81
end Sude.FastTwinScan
