import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B125 (S500..S503). -/
namespace Sude.FastTwinScan
namespace B125
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 1048576045 1050673197 = 6376 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 1048576045 1050673197).card = 6376 := by
  have h := fastStrideSixIntervalScan_spec 1048576045 1050673197 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 1050673197 1052770349 = 6389 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 1050673197 1052770349).card = 6389 := by
  have h := fastStrideSixIntervalScan_spec 1050673197 1052770349 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 1052770349 1054867501 = 6388 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 1052770349 1054867501).card = 6388 := by
  have h := fastStrideSixIntervalScan_spec 1052770349 1054867501 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 1054867501 1056964653 = 6349 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 1054867501 1056964653).card = 6349 := by
  have h := fastStrideSixIntervalScan_spec 1054867501 1056964653 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 1048576045 1052770349).card = 12765 := by
  simpa using combineTwinPrimeSegments (by decide : 1048576045 ≤ 1050673197) (by decide : 1050673197 ≤ 1052770349) seg0 seg1

theorem join23 : (twinPrimeSegment 1052770349 1056964653).card = 12737 := by
  simpa using combineTwinPrimeSegments (by decide : 1052770349 ≤ 1054867501) (by decide : 1054867501 ≤ 1056964653) seg2 seg3

theorem total : (twinPrimeSegment 1048576045 1056964653).card = 25502 := by
  simpa using combineTwinPrimeSegments (by decide : 1048576045 ≤ 1052770349) (by decide : 1052770349 ≤ 1056964653) join01 join23

end
end B125
end Sude.FastTwinScan
