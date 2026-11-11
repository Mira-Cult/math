import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B123 (S492..S495). -/
namespace Sude.FastTwinScan
namespace B123
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 1031798829 1033895981 = 6363 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 1031798829 1033895981).card = 6363 := by
  have h := fastStrideSixIntervalScan_spec 1031798829 1033895981 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 1033895981 1035993133 = 6364 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 1033895981 1035993133).card = 6364 := by
  have h := fastStrideSixIntervalScan_spec 1033895981 1035993133 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 1035993133 1038090285 = 6500 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 1035993133 1038090285).card = 6500 := by
  have h := fastStrideSixIntervalScan_spec 1035993133 1038090285 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 1038090285 1040187437 = 6486 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 1038090285 1040187437).card = 6486 := by
  have h := fastStrideSixIntervalScan_spec 1038090285 1040187437 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 1031798829 1035993133).card = 12727 := by
  simpa using combineTwinPrimeSegments (by decide : 1031798829 ≤ 1033895981) (by decide : 1033895981 ≤ 1035993133) seg0 seg1

theorem join23 : (twinPrimeSegment 1035993133 1040187437).card = 12986 := by
  simpa using combineTwinPrimeSegments (by decide : 1035993133 ≤ 1038090285) (by decide : 1038090285 ≤ 1040187437) seg2 seg3

theorem total : (twinPrimeSegment 1031798829 1040187437).card = 25713 := by
  simpa using combineTwinPrimeSegments (by decide : 1031798829 ≤ 1035993133) (by decide : 1035993133 ≤ 1040187437) join01 join23

end
end B123
end Sude.FastTwinScan
