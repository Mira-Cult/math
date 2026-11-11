import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B105 (S420..S423). -/
namespace Sude.FastTwinScan
namespace B105
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 880803885 882901037 = 6556 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 880803885 882901037).card = 6556 := by
  have h := fastStrideSixIntervalScan_spec 880803885 882901037 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 882901037 884998189 = 6507 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 882901037 884998189).card = 6507 := by
  have h := fastStrideSixIntervalScan_spec 882901037 884998189 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 884998189 887095341 = 6566 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 884998189 887095341).card = 6566 := by
  have h := fastStrideSixIntervalScan_spec 884998189 887095341 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 887095341 889192493 = 6558 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 887095341 889192493).card = 6558 := by
  have h := fastStrideSixIntervalScan_spec 887095341 889192493 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 880803885 884998189).card = 13063 := by
  simpa using combineTwinPrimeSegments (by decide : 880803885 ≤ 882901037) (by decide : 882901037 ≤ 884998189) seg0 seg1

theorem join23 : (twinPrimeSegment 884998189 889192493).card = 13124 := by
  simpa using combineTwinPrimeSegments (by decide : 884998189 ≤ 887095341) (by decide : 887095341 ≤ 889192493) seg2 seg3

theorem total : (twinPrimeSegment 880803885 889192493).card = 26187 := by
  simpa using combineTwinPrimeSegments (by decide : 880803885 ≤ 884998189) (by decide : 884998189 ≤ 889192493) join01 join23

end
end B105
end Sude.FastTwinScan
