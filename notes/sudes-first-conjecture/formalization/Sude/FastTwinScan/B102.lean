import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B102 (S408..S411). -/
namespace Sude.FastTwinScan
namespace B102
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 855638061 857735213 = 6454 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 855638061 857735213).card = 6454 := by
  have h := fastStrideSixIntervalScan_spec 855638061 857735213 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 857735213 859832365 = 6557 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 857735213 859832365).card = 6557 := by
  have h := fastStrideSixIntervalScan_spec 857735213 859832365 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 859832365 861929517 = 6639 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 859832365 861929517).card = 6639 := by
  have h := fastStrideSixIntervalScan_spec 859832365 861929517 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 861929517 864026669 = 6580 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 861929517 864026669).card = 6580 := by
  have h := fastStrideSixIntervalScan_spec 861929517 864026669 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 855638061 859832365).card = 13011 := by
  simpa using combineTwinPrimeSegments (by decide : 855638061 ≤ 857735213) (by decide : 857735213 ≤ 859832365) seg0 seg1

theorem join23 : (twinPrimeSegment 859832365 864026669).card = 13219 := by
  simpa using combineTwinPrimeSegments (by decide : 859832365 ≤ 861929517) (by decide : 861929517 ≤ 864026669) seg2 seg3

theorem total : (twinPrimeSegment 855638061 864026669).card = 26230 := by
  simpa using combineTwinPrimeSegments (by decide : 855638061 ≤ 859832365) (by decide : 859832365 ≤ 864026669) join01 join23

end
end B102
end Sude.FastTwinScan
