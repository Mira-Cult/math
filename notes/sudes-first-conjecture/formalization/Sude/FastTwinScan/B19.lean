import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B19 (S076..S079). -/
namespace Sude.FastTwinScan
namespace B19
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 159383597 161480749 = 7565 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 159383597 161480749).card = 7565 := by
  have h := fastStrideSixIntervalScan_spec 159383597 161480749 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 161480749 163577901 = 7651 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 161480749 163577901).card = 7651 := by
  have h := fastStrideSixIntervalScan_spec 161480749 163577901 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 163577901 165675053 = 7692 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 163577901 165675053).card = 7692 := by
  have h := fastStrideSixIntervalScan_spec 163577901 165675053 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 165675053 167772205 = 7748 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 165675053 167772205).card = 7748 := by
  have h := fastStrideSixIntervalScan_spec 165675053 167772205 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 159383597 163577901).card = 15216 := by
  simpa using combineTwinPrimeSegments (by decide : 159383597 ≤ 161480749) (by decide : 161480749 ≤ 163577901) seg0 seg1

theorem join23 : (twinPrimeSegment 163577901 167772205).card = 15440 := by
  simpa using combineTwinPrimeSegments (by decide : 163577901 ≤ 165675053) (by decide : 165675053 ≤ 167772205) seg2 seg3

theorem total : (twinPrimeSegment 159383597 167772205).card = 30656 := by
  simpa using combineTwinPrimeSegments (by decide : 159383597 ≤ 163577901) (by decide : 163577901 ≤ 167772205) join01 join23

end
end B19
end Sude.FastTwinScan
