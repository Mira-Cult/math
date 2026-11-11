import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B122 (S488..S491). -/
namespace Sude.FastTwinScan
namespace B122
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 1023410221 1025507373 = 6492 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 1023410221 1025507373).card = 6492 := by
  have h := fastStrideSixIntervalScan_spec 1023410221 1025507373 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 1025507373 1027604525 = 6231 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 1025507373 1027604525).card = 6231 := by
  have h := fastStrideSixIntervalScan_spec 1025507373 1027604525 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 1027604525 1029701677 = 6331 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 1027604525 1029701677).card = 6331 := by
  have h := fastStrideSixIntervalScan_spec 1027604525 1029701677 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 1029701677 1031798829 = 6458 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 1029701677 1031798829).card = 6458 := by
  have h := fastStrideSixIntervalScan_spec 1029701677 1031798829 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 1023410221 1027604525).card = 12723 := by
  simpa using combineTwinPrimeSegments (by decide : 1023410221 ≤ 1025507373) (by decide : 1025507373 ≤ 1027604525) seg0 seg1

theorem join23 : (twinPrimeSegment 1027604525 1031798829).card = 12789 := by
  simpa using combineTwinPrimeSegments (by decide : 1027604525 ≤ 1029701677) (by decide : 1029701677 ≤ 1031798829) seg2 seg3

theorem total : (twinPrimeSegment 1023410221 1031798829).card = 25512 := by
  simpa using combineTwinPrimeSegments (by decide : 1023410221 ≤ 1027604525) (by decide : 1027604525 ≤ 1031798829) join01 join23

end
end B122
end Sude.FastTwinScan
