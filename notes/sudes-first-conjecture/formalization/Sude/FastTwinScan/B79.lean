import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B79 (S316..S319). -/
namespace Sude.FastTwinScan
namespace B79
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 662700077 664797229 = 6689 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 662700077 664797229).card = 6689 := by
  have h := fastStrideSixIntervalScan_spec 662700077 664797229 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 664797229 666894381 = 6778 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 664797229 666894381).card = 6778 := by
  have h := fastStrideSixIntervalScan_spec 664797229 666894381 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 666894381 668991533 = 6736 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 666894381 668991533).card = 6736 := by
  have h := fastStrideSixIntervalScan_spec 666894381 668991533 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 668991533 671088685 = 6712 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 668991533 671088685).card = 6712 := by
  have h := fastStrideSixIntervalScan_spec 668991533 671088685 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 662700077 666894381).card = 13467 := by
  simpa using combineTwinPrimeSegments (by decide : 662700077 ≤ 664797229) (by decide : 664797229 ≤ 666894381) seg0 seg1

theorem join23 : (twinPrimeSegment 666894381 671088685).card = 13448 := by
  simpa using combineTwinPrimeSegments (by decide : 666894381 ≤ 668991533) (by decide : 668991533 ≤ 671088685) seg2 seg3

theorem total : (twinPrimeSegment 662700077 671088685).card = 26915 := by
  simpa using combineTwinPrimeSegments (by decide : 662700077 ≤ 666894381) (by decide : 666894381 ≤ 671088685) join01 join23

end
end B79
end Sude.FastTwinScan
