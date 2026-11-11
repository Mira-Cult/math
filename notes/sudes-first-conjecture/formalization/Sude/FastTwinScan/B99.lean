import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B99 (S396..S399). -/
namespace Sude.FastTwinScan
namespace B99
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 830472237 832569389 = 6585 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 830472237 832569389).card = 6585 := by
  have h := fastStrideSixIntervalScan_spec 830472237 832569389 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 832569389 834666541 = 6572 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 832569389 834666541).card = 6572 := by
  have h := fastStrideSixIntervalScan_spec 832569389 834666541 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 834666541 836763693 = 6563 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 834666541 836763693).card = 6563 := by
  have h := fastStrideSixIntervalScan_spec 834666541 836763693 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 836763693 838860845 = 6638 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 836763693 838860845).card = 6638 := by
  have h := fastStrideSixIntervalScan_spec 836763693 838860845 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 830472237 834666541).card = 13157 := by
  simpa using combineTwinPrimeSegments (by decide : 830472237 ≤ 832569389) (by decide : 832569389 ≤ 834666541) seg0 seg1

theorem join23 : (twinPrimeSegment 834666541 838860845).card = 13201 := by
  simpa using combineTwinPrimeSegments (by decide : 834666541 ≤ 836763693) (by decide : 836763693 ≤ 838860845) seg2 seg3

theorem total : (twinPrimeSegment 830472237 838860845).card = 26358 := by
  simpa using combineTwinPrimeSegments (by decide : 830472237 ≤ 834666541) (by decide : 834666541 ≤ 838860845) join01 join23

end
end B99
end Sude.FastTwinScan
