import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B31 (S124..S127). -/
namespace Sude.FastTwinScan
namespace B31
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 260046893 262144045 = 7575 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 260046893 262144045).card = 7575 := by
  have h := fastStrideSixIntervalScan_spec 260046893 262144045 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 262144045 264241197 = 7320 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 262144045 264241197).card = 7320 := by
  have h := fastStrideSixIntervalScan_spec 262144045 264241197 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 264241197 266338349 = 7399 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 264241197 266338349).card = 7399 := by
  have h := fastStrideSixIntervalScan_spec 264241197 266338349 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 266338349 268435501 = 7223 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 266338349 268435501).card = 7223 := by
  have h := fastStrideSixIntervalScan_spec 266338349 268435501 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 260046893 264241197).card = 14895 := by
  simpa using combineTwinPrimeSegments (by decide : 260046893 ≤ 262144045) (by decide : 262144045 ≤ 264241197) seg0 seg1

theorem join23 : (twinPrimeSegment 264241197 268435501).card = 14622 := by
  simpa using combineTwinPrimeSegments (by decide : 264241197 ≤ 266338349) (by decide : 266338349 ≤ 268435501) seg2 seg3

theorem total : (twinPrimeSegment 260046893 268435501).card = 29517 := by
  simpa using combineTwinPrimeSegments (by decide : 260046893 ≤ 264241197) (by decide : 264241197 ≤ 268435501) join01 join23

end
end B31
end Sude.FastTwinScan
