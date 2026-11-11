import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B47 (S188..S191). -/
namespace Sude.FastTwinScan
namespace B47
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 394264621 396361773 = 7038 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 394264621 396361773).card = 7038 := by
  have h := fastStrideSixIntervalScan_spec 394264621 396361773 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 396361773 398458925 = 7081 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 396361773 398458925).card = 7081 := by
  have h := fastStrideSixIntervalScan_spec 396361773 398458925 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 398458925 400556077 = 7015 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 398458925 400556077).card = 7015 := by
  have h := fastStrideSixIntervalScan_spec 398458925 400556077 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 400556077 402653229 = 7068 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 400556077 402653229).card = 7068 := by
  have h := fastStrideSixIntervalScan_spec 400556077 402653229 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 394264621 398458925).card = 14119 := by
  simpa using combineTwinPrimeSegments (by decide : 394264621 ≤ 396361773) (by decide : 396361773 ≤ 398458925) seg0 seg1

theorem join23 : (twinPrimeSegment 398458925 402653229).card = 14083 := by
  simpa using combineTwinPrimeSegments (by decide : 398458925 ≤ 400556077) (by decide : 400556077 ≤ 402653229) seg2 seg3

theorem total : (twinPrimeSegment 394264621 402653229).card = 28202 := by
  simpa using combineTwinPrimeSegments (by decide : 394264621 ≤ 398458925) (by decide : 398458925 ≤ 402653229) join01 join23

end
end B47
end Sude.FastTwinScan
