import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B29 (S116..S119). -/
namespace Sude.FastTwinScan
namespace B29
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 243269677 245366829 = 7480 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 243269677 245366829).card = 7480 := by
  have h := fastStrideSixIntervalScan_spec 243269677 245366829 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 245366829 247463981 = 7295 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 245366829 247463981).card = 7295 := by
  have h := fastStrideSixIntervalScan_spec 245366829 247463981 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 247463981 249561133 = 7365 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 247463981 249561133).card = 7365 := by
  have h := fastStrideSixIntervalScan_spec 247463981 249561133 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 249561133 251658285 = 7373 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 249561133 251658285).card = 7373 := by
  have h := fastStrideSixIntervalScan_spec 249561133 251658285 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 243269677 247463981).card = 14775 := by
  simpa using combineTwinPrimeSegments (by decide : 243269677 ≤ 245366829) (by decide : 245366829 ≤ 247463981) seg0 seg1

theorem join23 : (twinPrimeSegment 247463981 251658285).card = 14738 := by
  simpa using combineTwinPrimeSegments (by decide : 247463981 ≤ 249561133) (by decide : 249561133 ≤ 251658285) seg2 seg3

theorem total : (twinPrimeSegment 243269677 251658285).card = 29513 := by
  simpa using combineTwinPrimeSegments (by decide : 243269677 ≤ 247463981) (by decide : 247463981 ≤ 251658285) join01 join23

end
end B29
end Sude.FastTwinScan
