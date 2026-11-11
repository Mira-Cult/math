import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B70 (S280..S283). -/
namespace Sude.FastTwinScan
namespace B70
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 587202605 589299757 = 6892 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 587202605 589299757).card = 6892 := by
  have h := fastStrideSixIntervalScan_spec 587202605 589299757 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 589299757 591396909 = 6741 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 589299757 591396909).card = 6741 := by
  have h := fastStrideSixIntervalScan_spec 589299757 591396909 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 591396909 593494061 = 6769 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 591396909 593494061).card = 6769 := by
  have h := fastStrideSixIntervalScan_spec 591396909 593494061 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 593494061 595591213 = 6781 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 593494061 595591213).card = 6781 := by
  have h := fastStrideSixIntervalScan_spec 593494061 595591213 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 587202605 591396909).card = 13633 := by
  simpa using combineTwinPrimeSegments (by decide : 587202605 ≤ 589299757) (by decide : 589299757 ≤ 591396909) seg0 seg1

theorem join23 : (twinPrimeSegment 591396909 595591213).card = 13550 := by
  simpa using combineTwinPrimeSegments (by decide : 591396909 ≤ 593494061) (by decide : 593494061 ≤ 595591213) seg2 seg3

theorem total : (twinPrimeSegment 587202605 595591213).card = 27183 := by
  simpa using combineTwinPrimeSegments (by decide : 587202605 ≤ 591396909) (by decide : 591396909 ≤ 595591213) join01 join23

end
end B70
end Sude.FastTwinScan
