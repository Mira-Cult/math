import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B104 (S416..S419). -/
namespace Sude.FastTwinScan
namespace B104
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 872415277 874512429 = 6536 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 872415277 874512429).card = 6536 := by
  have h := fastStrideSixIntervalScan_spec 872415277 874512429 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 874512429 876609581 = 6557 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 874512429 876609581).card = 6557 := by
  have h := fastStrideSixIntervalScan_spec 874512429 876609581 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 876609581 878706733 = 6544 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 876609581 878706733).card = 6544 := by
  have h := fastStrideSixIntervalScan_spec 876609581 878706733 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 878706733 880803885 = 6446 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 878706733 880803885).card = 6446 := by
  have h := fastStrideSixIntervalScan_spec 878706733 880803885 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 872415277 876609581).card = 13093 := by
  simpa using combineTwinPrimeSegments (by decide : 872415277 ≤ 874512429) (by decide : 874512429 ≤ 876609581) seg0 seg1

theorem join23 : (twinPrimeSegment 876609581 880803885).card = 12990 := by
  simpa using combineTwinPrimeSegments (by decide : 876609581 ≤ 878706733) (by decide : 878706733 ≤ 880803885) seg2 seg3

theorem total : (twinPrimeSegment 872415277 880803885).card = 26083 := by
  simpa using combineTwinPrimeSegments (by decide : 872415277 ≤ 876609581) (by decide : 876609581 ≤ 880803885) join01 join23

end
end B104
end Sude.FastTwinScan
