import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B25 (S100..S103). -/
namespace Sude.FastTwinScan
namespace B25
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 209715245 211812397 = 7548 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 209715245 211812397).card = 7548 := by
  have h := fastStrideSixIntervalScan_spec 209715245 211812397 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 211812397 213909549 = 7520 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 211812397 213909549).card = 7520 := by
  have h := fastStrideSixIntervalScan_spec 211812397 213909549 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 213909549 216006701 = 7542 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 213909549 216006701).card = 7542 := by
  have h := fastStrideSixIntervalScan_spec 213909549 216006701 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 216006701 218103853 = 7361 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 216006701 218103853).card = 7361 := by
  have h := fastStrideSixIntervalScan_spec 216006701 218103853 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 209715245 213909549).card = 15068 := by
  simpa using combineTwinPrimeSegments (by decide : 209715245 ≤ 211812397) (by decide : 211812397 ≤ 213909549) seg0 seg1

theorem join23 : (twinPrimeSegment 213909549 218103853).card = 14903 := by
  simpa using combineTwinPrimeSegments (by decide : 213909549 ≤ 216006701) (by decide : 216006701 ≤ 218103853) seg2 seg3

theorem total : (twinPrimeSegment 209715245 218103853).card = 29971 := by
  simpa using combineTwinPrimeSegments (by decide : 209715245 ≤ 213909549) (by decide : 213909549 ≤ 218103853) join01 join23

end
end B25
end Sude.FastTwinScan
