import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B95 (S380..S383). -/
namespace Sude.FastTwinScan
namespace B95
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 796917805 799014957 = 6655 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 796917805 799014957).card = 6655 := by
  have h := fastStrideSixIntervalScan_spec 796917805 799014957 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 799014957 801112109 = 6528 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 799014957 801112109).card = 6528 := by
  have h := fastStrideSixIntervalScan_spec 799014957 801112109 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 801112109 803209261 = 6525 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 801112109 803209261).card = 6525 := by
  have h := fastStrideSixIntervalScan_spec 801112109 803209261 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 803209261 805306413 = 6606 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 803209261 805306413).card = 6606 := by
  have h := fastStrideSixIntervalScan_spec 803209261 805306413 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 796917805 801112109).card = 13183 := by
  simpa using combineTwinPrimeSegments (by decide : 796917805 ≤ 799014957) (by decide : 799014957 ≤ 801112109) seg0 seg1

theorem join23 : (twinPrimeSegment 801112109 805306413).card = 13131 := by
  simpa using combineTwinPrimeSegments (by decide : 801112109 ≤ 803209261) (by decide : 803209261 ≤ 805306413) seg2 seg3

theorem total : (twinPrimeSegment 796917805 805306413).card = 26314 := by
  simpa using combineTwinPrimeSegments (by decide : 796917805 ≤ 801112109) (by decide : 801112109 ≤ 805306413) join01 join23

end
end B95
end Sude.FastTwinScan
