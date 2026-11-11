import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B124 (S496..S499). -/
namespace Sude.FastTwinScan
namespace B124
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 1040187437 1042284589 = 6492 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 1040187437 1042284589).card = 6492 := by
  have h := fastStrideSixIntervalScan_spec 1040187437 1042284589 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 1042284589 1044381741 = 6444 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 1042284589 1044381741).card = 6444 := by
  have h := fastStrideSixIntervalScan_spec 1042284589 1044381741 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 1044381741 1046478893 = 6347 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 1044381741 1046478893).card = 6347 := by
  have h := fastStrideSixIntervalScan_spec 1044381741 1046478893 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 1046478893 1048576045 = 6435 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 1046478893 1048576045).card = 6435 := by
  have h := fastStrideSixIntervalScan_spec 1046478893 1048576045 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 1040187437 1044381741).card = 12936 := by
  simpa using combineTwinPrimeSegments (by decide : 1040187437 ≤ 1042284589) (by decide : 1042284589 ≤ 1044381741) seg0 seg1

theorem join23 : (twinPrimeSegment 1044381741 1048576045).card = 12782 := by
  simpa using combineTwinPrimeSegments (by decide : 1044381741 ≤ 1046478893) (by decide : 1046478893 ≤ 1048576045) seg2 seg3

theorem total : (twinPrimeSegment 1040187437 1048576045).card = 25718 := by
  simpa using combineTwinPrimeSegments (by decide : 1040187437 ≤ 1044381741) (by decide : 1044381741 ≤ 1048576045) join01 join23

end
end B124
end Sude.FastTwinScan
