import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B61 (S244..S247). -/
namespace Sude.FastTwinScan
namespace B61
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 511705133 513802285 = 6882 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 511705133 513802285).card = 6882 := by
  have h := fastStrideSixIntervalScan_spec 511705133 513802285 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 513802285 515899437 = 6867 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 513802285 515899437).card = 6867 := by
  have h := fastStrideSixIntervalScan_spec 513802285 515899437 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 515899437 517996589 = 6862 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 515899437 517996589).card = 6862 := by
  have h := fastStrideSixIntervalScan_spec 515899437 517996589 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 517996589 520093741 = 6940 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 517996589 520093741).card = 6940 := by
  have h := fastStrideSixIntervalScan_spec 517996589 520093741 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 511705133 515899437).card = 13749 := by
  simpa using combineTwinPrimeSegments (by decide : 511705133 ≤ 513802285) (by decide : 513802285 ≤ 515899437) seg0 seg1

theorem join23 : (twinPrimeSegment 515899437 520093741).card = 13802 := by
  simpa using combineTwinPrimeSegments (by decide : 515899437 ≤ 517996589) (by decide : 517996589 ≤ 520093741) seg2 seg3

theorem total : (twinPrimeSegment 511705133 520093741).card = 27551 := by
  simpa using combineTwinPrimeSegments (by decide : 511705133 ≤ 515899437) (by decide : 515899437 ≤ 520093741) join01 join23

end
end B61
end Sude.FastTwinScan
