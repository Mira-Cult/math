import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B04 (S016..S019). -/
namespace Sude.FastTwinScan
namespace B04
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 33554477 35651629 = 9117 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 33554477 35651629).card = 9117 := by
  have h := fastStrideSixIntervalScan_spec 33554477 35651629 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 35651629 37748781 = 9252 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 35651629 37748781).card = 9252 := by
  have h := fastStrideSixIntervalScan_spec 35651629 37748781 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 37748781 39845933 = 9121 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 37748781 39845933).card = 9121 := by
  have h := fastStrideSixIntervalScan_spec 37748781 39845933 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 39845933 41943085 = 8912 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 39845933 41943085).card = 8912 := by
  have h := fastStrideSixIntervalScan_spec 39845933 41943085 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 33554477 37748781).card = 18369 := by
  simpa using combineTwinPrimeSegments (by decide : 33554477 ≤ 35651629) (by decide : 35651629 ≤ 37748781) seg0 seg1

theorem join23 : (twinPrimeSegment 37748781 41943085).card = 18033 := by
  simpa using combineTwinPrimeSegments (by decide : 37748781 ≤ 39845933) (by decide : 39845933 ≤ 41943085) seg2 seg3

theorem total : (twinPrimeSegment 33554477 41943085).card = 36402 := by
  simpa using combineTwinPrimeSegments (by decide : 33554477 ≤ 37748781) (by decide : 37748781 ≤ 41943085) join01 join23

end
end B04
end Sude.FastTwinScan
