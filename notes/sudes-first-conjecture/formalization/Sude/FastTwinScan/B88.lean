import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B88 (S352..S355). -/
namespace Sude.FastTwinScan
namespace B88
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 738197549 740294701 = 6657 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 738197549 740294701).card = 6657 := by
  have h := fastStrideSixIntervalScan_spec 738197549 740294701 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 740294701 742391853 = 6731 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 740294701 742391853).card = 6731 := by
  have h := fastStrideSixIntervalScan_spec 740294701 742391853 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 742391853 744489005 = 6579 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 742391853 744489005).card = 6579 := by
  have h := fastStrideSixIntervalScan_spec 742391853 744489005 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 744489005 746586157 = 6615 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 744489005 746586157).card = 6615 := by
  have h := fastStrideSixIntervalScan_spec 744489005 746586157 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 738197549 742391853).card = 13388 := by
  simpa using combineTwinPrimeSegments (by decide : 738197549 ≤ 740294701) (by decide : 740294701 ≤ 742391853) seg0 seg1

theorem join23 : (twinPrimeSegment 742391853 746586157).card = 13194 := by
  simpa using combineTwinPrimeSegments (by decide : 742391853 ≤ 744489005) (by decide : 744489005 ≤ 746586157) seg2 seg3

theorem total : (twinPrimeSegment 738197549 746586157).card = 26582 := by
  simpa using combineTwinPrimeSegments (by decide : 738197549 ≤ 742391853) (by decide : 742391853 ≤ 746586157) join01 join23

end
end B88
end Sude.FastTwinScan
