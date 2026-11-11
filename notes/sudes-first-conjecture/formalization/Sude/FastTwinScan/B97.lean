import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B97 (S388..S391). -/
namespace Sude.FastTwinScan
namespace B97
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 813695021 815792173 = 6613 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 813695021 815792173).card = 6613 := by
  have h := fastStrideSixIntervalScan_spec 813695021 815792173 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 815792173 817889325 = 6488 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 815792173 817889325).card = 6488 := by
  have h := fastStrideSixIntervalScan_spec 815792173 817889325 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 817889325 819986477 = 6526 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 817889325 819986477).card = 6526 := by
  have h := fastStrideSixIntervalScan_spec 817889325 819986477 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 819986477 822083629 = 6573 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 819986477 822083629).card = 6573 := by
  have h := fastStrideSixIntervalScan_spec 819986477 822083629 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 813695021 817889325).card = 13101 := by
  simpa using combineTwinPrimeSegments (by decide : 813695021 ≤ 815792173) (by decide : 815792173 ≤ 817889325) seg0 seg1

theorem join23 : (twinPrimeSegment 817889325 822083629).card = 13099 := by
  simpa using combineTwinPrimeSegments (by decide : 817889325 ≤ 819986477) (by decide : 819986477 ≤ 822083629) seg2 seg3

theorem total : (twinPrimeSegment 813695021 822083629).card = 26200 := by
  simpa using combineTwinPrimeSegments (by decide : 813695021 ≤ 817889325) (by decide : 817889325 ≤ 822083629) join01 join23

end
end B97
end Sude.FastTwinScan
