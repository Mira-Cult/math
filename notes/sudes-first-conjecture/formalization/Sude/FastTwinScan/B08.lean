import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B08 (S032..S035). -/
namespace Sude.FastTwinScan
namespace B08
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 67108909 69206061 = 8615 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 67108909 69206061).card = 8615 := by
  have h := fastStrideSixIntervalScan_spec 67108909 69206061 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 69206061 71303213 = 8494 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 69206061 71303213).card = 8494 := by
  have h := fastStrideSixIntervalScan_spec 69206061 71303213 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 71303213 73400365 = 8374 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 71303213 73400365).card = 8374 := by
  have h := fastStrideSixIntervalScan_spec 71303213 73400365 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 73400365 75497517 = 8445 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 73400365 75497517).card = 8445 := by
  have h := fastStrideSixIntervalScan_spec 73400365 75497517 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 67108909 71303213).card = 17109 := by
  simpa using combineTwinPrimeSegments (by decide : 67108909 ≤ 69206061) (by decide : 69206061 ≤ 71303213) seg0 seg1

theorem join23 : (twinPrimeSegment 71303213 75497517).card = 16819 := by
  simpa using combineTwinPrimeSegments (by decide : 71303213 ≤ 73400365) (by decide : 73400365 ≤ 75497517) seg2 seg3

theorem total : (twinPrimeSegment 67108909 75497517).card = 33928 := by
  simpa using combineTwinPrimeSegments (by decide : 67108909 ≤ 71303213) (by decide : 71303213 ≤ 75497517) join01 join23

end
end B08
end Sude.FastTwinScan
