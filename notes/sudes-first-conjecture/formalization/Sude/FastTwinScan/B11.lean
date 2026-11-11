import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B11 (S044..S047). -/
namespace Sude.FastTwinScan
namespace B11
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 92274733 94371885 = 8180 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 92274733 94371885).card = 8180 := by
  have h := fastStrideSixIntervalScan_spec 92274733 94371885 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 94371885 96469037 = 8198 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 94371885 96469037).card = 8198 := by
  have h := fastStrideSixIntervalScan_spec 94371885 96469037 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 96469037 98566189 = 8202 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 96469037 98566189).card = 8202 := by
  have h := fastStrideSixIntervalScan_spec 96469037 98566189 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 98566189 100663341 = 8221 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 98566189 100663341).card = 8221 := by
  have h := fastStrideSixIntervalScan_spec 98566189 100663341 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 92274733 96469037).card = 16378 := by
  simpa using combineTwinPrimeSegments (by decide : 92274733 ≤ 94371885) (by decide : 94371885 ≤ 96469037) seg0 seg1

theorem join23 : (twinPrimeSegment 96469037 100663341).card = 16423 := by
  simpa using combineTwinPrimeSegments (by decide : 96469037 ≤ 98566189) (by decide : 98566189 ≤ 100663341) seg2 seg3

theorem total : (twinPrimeSegment 92274733 100663341).card = 32801 := by
  simpa using combineTwinPrimeSegments (by decide : 92274733 ≤ 96469037) (by decide : 96469037 ≤ 100663341) join01 join23

end
end B11
end Sude.FastTwinScan
