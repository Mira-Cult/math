import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B119 (S476..S479). -/
namespace Sude.FastTwinScan
namespace B119
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 998244397 1000341549 = 6536 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 998244397 1000341549).card = 6536 := by
  have h := fastStrideSixIntervalScan_spec 998244397 1000341549 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 1000341549 1002438701 = 6378 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 1000341549 1002438701).card = 6378 := by
  have h := fastStrideSixIntervalScan_spec 1000341549 1002438701 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 1002438701 1004535853 = 6468 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 1002438701 1004535853).card = 6468 := by
  have h := fastStrideSixIntervalScan_spec 1002438701 1004535853 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 1004535853 1006633005 = 6465 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 1004535853 1006633005).card = 6465 := by
  have h := fastStrideSixIntervalScan_spec 1004535853 1006633005 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 998244397 1002438701).card = 12914 := by
  simpa using combineTwinPrimeSegments (by decide : 998244397 ≤ 1000341549) (by decide : 1000341549 ≤ 1002438701) seg0 seg1

theorem join23 : (twinPrimeSegment 1002438701 1006633005).card = 12933 := by
  simpa using combineTwinPrimeSegments (by decide : 1002438701 ≤ 1004535853) (by decide : 1004535853 ≤ 1006633005) seg2 seg3

theorem total : (twinPrimeSegment 998244397 1006633005).card = 25847 := by
  simpa using combineTwinPrimeSegments (by decide : 998244397 ≤ 1002438701) (by decide : 1002438701 ≤ 1006633005) join01 join23

end
end B119
end Sude.FastTwinScan
