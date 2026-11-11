import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B26 (S104..S107). -/
namespace Sude.FastTwinScan
namespace B26
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 218103853 220201005 = 7412 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 218103853 220201005).card = 7412 := by
  have h := fastStrideSixIntervalScan_spec 218103853 220201005 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 220201005 222298157 = 7530 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 220201005 222298157).card = 7530 := by
  have h := fastStrideSixIntervalScan_spec 220201005 222298157 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 222298157 224395309 = 7622 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 222298157 224395309).card = 7622 := by
  have h := fastStrideSixIntervalScan_spec 222298157 224395309 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 224395309 226492461 = 7357 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 224395309 226492461).card = 7357 := by
  have h := fastStrideSixIntervalScan_spec 224395309 226492461 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 218103853 222298157).card = 14942 := by
  simpa using combineTwinPrimeSegments (by decide : 218103853 ≤ 220201005) (by decide : 220201005 ≤ 222298157) seg0 seg1

theorem join23 : (twinPrimeSegment 222298157 226492461).card = 14979 := by
  simpa using combineTwinPrimeSegments (by decide : 222298157 ≤ 224395309) (by decide : 224395309 ≤ 226492461) seg2 seg3

theorem total : (twinPrimeSegment 218103853 226492461).card = 29921 := by
  simpa using combineTwinPrimeSegments (by decide : 218103853 ≤ 222298157) (by decide : 222298157 ≤ 226492461) join01 join23

end
end B26
end Sude.FastTwinScan
