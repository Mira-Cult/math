import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B42 (S168..S171). -/
namespace Sude.FastTwinScan
namespace B42
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 352321581 354418733 = 7060 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 352321581 354418733).card = 7060 := by
  have h := fastStrideSixIntervalScan_spec 352321581 354418733 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 354418733 356515885 = 7198 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 354418733 356515885).card = 7198 := by
  have h := fastStrideSixIntervalScan_spec 354418733 356515885 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 356515885 358613037 = 7055 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 356515885 358613037).card = 7055 := by
  have h := fastStrideSixIntervalScan_spec 356515885 358613037 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 358613037 360710189 = 7060 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 358613037 360710189).card = 7060 := by
  have h := fastStrideSixIntervalScan_spec 358613037 360710189 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 352321581 356515885).card = 14258 := by
  simpa using combineTwinPrimeSegments (by decide : 352321581 ≤ 354418733) (by decide : 354418733 ≤ 356515885) seg0 seg1

theorem join23 : (twinPrimeSegment 356515885 360710189).card = 14115 := by
  simpa using combineTwinPrimeSegments (by decide : 356515885 ≤ 358613037) (by decide : 358613037 ≤ 360710189) seg2 seg3

theorem total : (twinPrimeSegment 352321581 360710189).card = 28373 := by
  simpa using combineTwinPrimeSegments (by decide : 352321581 ≤ 356515885) (by decide : 356515885 ≤ 360710189) join01 join23

end
end B42
end Sude.FastTwinScan
