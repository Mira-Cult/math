import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B24 (S096..S099). -/
namespace Sude.FastTwinScan
namespace B24
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 201326637 203423789 = 7440 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 201326637 203423789).card = 7440 := by
  have h := fastStrideSixIntervalScan_spec 201326637 203423789 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 203423789 205520941 = 7566 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 203423789 205520941).card = 7566 := by
  have h := fastStrideSixIntervalScan_spec 203423789 205520941 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 205520941 207618093 = 7531 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 205520941 207618093).card = 7531 := by
  have h := fastStrideSixIntervalScan_spec 205520941 207618093 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 207618093 209715245 = 7619 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 207618093 209715245).card = 7619 := by
  have h := fastStrideSixIntervalScan_spec 207618093 209715245 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 201326637 205520941).card = 15006 := by
  simpa using combineTwinPrimeSegments (by decide : 201326637 ≤ 203423789) (by decide : 203423789 ≤ 205520941) seg0 seg1

theorem join23 : (twinPrimeSegment 205520941 209715245).card = 15150 := by
  simpa using combineTwinPrimeSegments (by decide : 205520941 ≤ 207618093) (by decide : 207618093 ≤ 209715245) seg2 seg3

theorem total : (twinPrimeSegment 201326637 209715245).card = 30156 := by
  simpa using combineTwinPrimeSegments (by decide : 201326637 ≤ 205520941) (by decide : 205520941 ≤ 209715245) join01 join23

end
end B24
end Sude.FastTwinScan
