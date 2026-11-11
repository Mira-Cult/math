import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B93 (S372..S375). -/
namespace Sude.FastTwinScan
namespace B93
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 780140589 782237741 = 6621 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 780140589 782237741).card = 6621 := by
  have h := fastStrideSixIntervalScan_spec 780140589 782237741 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 782237741 784334893 = 6581 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 782237741 784334893).card = 6581 := by
  have h := fastStrideSixIntervalScan_spec 782237741 784334893 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 784334893 786432045 = 6595 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 784334893 786432045).card = 6595 := by
  have h := fastStrideSixIntervalScan_spec 784334893 786432045 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 786432045 788529197 = 6403 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 786432045 788529197).card = 6403 := by
  have h := fastStrideSixIntervalScan_spec 786432045 788529197 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 780140589 784334893).card = 13202 := by
  simpa using combineTwinPrimeSegments (by decide : 780140589 ≤ 782237741) (by decide : 782237741 ≤ 784334893) seg0 seg1

theorem join23 : (twinPrimeSegment 784334893 788529197).card = 12998 := by
  simpa using combineTwinPrimeSegments (by decide : 784334893 ≤ 786432045) (by decide : 786432045 ≤ 788529197) seg2 seg3

theorem total : (twinPrimeSegment 780140589 788529197).card = 26200 := by
  simpa using combineTwinPrimeSegments (by decide : 780140589 ≤ 784334893) (by decide : 784334893 ≤ 788529197) join01 join23

end
end B93
end Sude.FastTwinScan
