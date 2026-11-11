import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B15 (S060..S063). -/
namespace Sude.FastTwinScan
namespace B15
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 125829165 127926317 = 7948 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 125829165 127926317).card = 7948 := by
  have h := fastStrideSixIntervalScan_spec 125829165 127926317 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 127926317 130023469 = 8026 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 127926317 130023469).card = 8026 := by
  have h := fastStrideSixIntervalScan_spec 127926317 130023469 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 130023469 132120621 = 7943 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 130023469 132120621).card = 7943 := by
  have h := fastStrideSixIntervalScan_spec 130023469 132120621 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 132120621 134217773 = 7899 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 132120621 134217773).card = 7899 := by
  have h := fastStrideSixIntervalScan_spec 132120621 134217773 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 125829165 130023469).card = 15974 := by
  simpa using combineTwinPrimeSegments (by decide : 125829165 ≤ 127926317) (by decide : 127926317 ≤ 130023469) seg0 seg1

theorem join23 : (twinPrimeSegment 130023469 134217773).card = 15842 := by
  simpa using combineTwinPrimeSegments (by decide : 130023469 ≤ 132120621) (by decide : 132120621 ≤ 134217773) seg2 seg3

theorem total : (twinPrimeSegment 125829165 134217773).card = 31816 := by
  simpa using combineTwinPrimeSegments (by decide : 125829165 ≤ 130023469) (by decide : 130023469 ≤ 134217773) join01 join23

end
end B15
end Sude.FastTwinScan
