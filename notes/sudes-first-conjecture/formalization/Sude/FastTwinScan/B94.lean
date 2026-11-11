import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B94 (S376..S379). -/
namespace Sude.FastTwinScan
namespace B94
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 788529197 790626349 = 6621 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 788529197 790626349).card = 6621 := by
  have h := fastStrideSixIntervalScan_spec 788529197 790626349 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 790626349 792723501 = 6655 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 790626349 792723501).card = 6655 := by
  have h := fastStrideSixIntervalScan_spec 790626349 792723501 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 792723501 794820653 = 6572 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 792723501 794820653).card = 6572 := by
  have h := fastStrideSixIntervalScan_spec 792723501 794820653 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 794820653 796917805 = 6496 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 794820653 796917805).card = 6496 := by
  have h := fastStrideSixIntervalScan_spec 794820653 796917805 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 788529197 792723501).card = 13276 := by
  simpa using combineTwinPrimeSegments (by decide : 788529197 ≤ 790626349) (by decide : 790626349 ≤ 792723501) seg0 seg1

theorem join23 : (twinPrimeSegment 792723501 796917805).card = 13068 := by
  simpa using combineTwinPrimeSegments (by decide : 792723501 ≤ 794820653) (by decide : 794820653 ≤ 796917805) seg2 seg3

theorem total : (twinPrimeSegment 788529197 796917805).card = 26344 := by
  simpa using combineTwinPrimeSegments (by decide : 788529197 ≤ 792723501) (by decide : 792723501 ≤ 796917805) join01 join23

end
end B94
end Sude.FastTwinScan
