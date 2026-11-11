import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B56 (S224..S227). -/
namespace Sude.FastTwinScan
namespace B56
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 469762093 471859245 = 7006 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 469762093 471859245).card = 7006 := by
  have h := fastStrideSixIntervalScan_spec 469762093 471859245 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 471859245 473956397 = 6860 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 471859245 473956397).card = 6860 := by
  have h := fastStrideSixIntervalScan_spec 471859245 473956397 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 473956397 476053549 = 6940 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 473956397 476053549).card = 6940 := by
  have h := fastStrideSixIntervalScan_spec 473956397 476053549 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 476053549 478150701 = 6983 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 476053549 478150701).card = 6983 := by
  have h := fastStrideSixIntervalScan_spec 476053549 478150701 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 469762093 473956397).card = 13866 := by
  simpa using combineTwinPrimeSegments (by decide : 469762093 ≤ 471859245) (by decide : 471859245 ≤ 473956397) seg0 seg1

theorem join23 : (twinPrimeSegment 473956397 478150701).card = 13923 := by
  simpa using combineTwinPrimeSegments (by decide : 473956397 ≤ 476053549) (by decide : 476053549 ≤ 478150701) seg2 seg3

theorem total : (twinPrimeSegment 469762093 478150701).card = 27789 := by
  simpa using combineTwinPrimeSegments (by decide : 469762093 ≤ 473956397) (by decide : 473956397 ≤ 478150701) join01 join23

end
end B56
end Sude.FastTwinScan
