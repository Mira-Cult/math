import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B05 (S020..S023). -/
namespace Sude.FastTwinScan
namespace B05
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 41943085 44040237 = 8887 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 41943085 44040237).card = 8887 := by
  have h := fastStrideSixIntervalScan_spec 41943085 44040237 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 44040237 46137389 = 8912 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 44040237 46137389).card = 8912 := by
  have h := fastStrideSixIntervalScan_spec 44040237 46137389 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 46137389 48234541 = 8825 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 46137389 48234541).card = 8825 := by
  have h := fastStrideSixIntervalScan_spec 46137389 48234541 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 48234541 50331693 = 8778 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 48234541 50331693).card = 8778 := by
  have h := fastStrideSixIntervalScan_spec 48234541 50331693 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 41943085 46137389).card = 17799 := by
  simpa using combineTwinPrimeSegments (by decide : 41943085 ≤ 44040237) (by decide : 44040237 ≤ 46137389) seg0 seg1

theorem join23 : (twinPrimeSegment 46137389 50331693).card = 17603 := by
  simpa using combineTwinPrimeSegments (by decide : 46137389 ≤ 48234541) (by decide : 48234541 ≤ 50331693) seg2 seg3

theorem total : (twinPrimeSegment 41943085 50331693).card = 35402 := by
  simpa using combineTwinPrimeSegments (by decide : 41943085 ≤ 46137389) (by decide : 46137389 ≤ 50331693) join01 join23

end
end B05
end Sude.FastTwinScan
