import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B120 (S480..S483). -/
namespace Sude.FastTwinScan
namespace B120
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 1006633005 1008730157 = 6443 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 1006633005 1008730157).card = 6443 := by
  have h := fastStrideSixIntervalScan_spec 1006633005 1008730157 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 1008730157 1010827309 = 6467 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 1008730157 1010827309).card = 6467 := by
  have h := fastStrideSixIntervalScan_spec 1008730157 1010827309 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 1010827309 1012924461 = 6479 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 1010827309 1012924461).card = 6479 := by
  have h := fastStrideSixIntervalScan_spec 1010827309 1012924461 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 1012924461 1015021613 = 6443 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 1012924461 1015021613).card = 6443 := by
  have h := fastStrideSixIntervalScan_spec 1012924461 1015021613 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 1006633005 1010827309).card = 12910 := by
  simpa using combineTwinPrimeSegments (by decide : 1006633005 ≤ 1008730157) (by decide : 1008730157 ≤ 1010827309) seg0 seg1

theorem join23 : (twinPrimeSegment 1010827309 1015021613).card = 12922 := by
  simpa using combineTwinPrimeSegments (by decide : 1010827309 ≤ 1012924461) (by decide : 1012924461 ≤ 1015021613) seg2 seg3

theorem total : (twinPrimeSegment 1006633005 1015021613).card = 25832 := by
  simpa using combineTwinPrimeSegments (by decide : 1006633005 ≤ 1010827309) (by decide : 1010827309 ≤ 1015021613) join01 join23

end
end B120
end Sude.FastTwinScan
