import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B106 (S424..S427). -/
namespace Sude.FastTwinScan
namespace B106
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 889192493 891289645 = 6605 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 889192493 891289645).card = 6605 := by
  have h := fastStrideSixIntervalScan_spec 889192493 891289645 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 891289645 893386797 = 6475 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 891289645 893386797).card = 6475 := by
  have h := fastStrideSixIntervalScan_spec 891289645 893386797 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 893386797 895483949 = 6526 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 893386797 895483949).card = 6526 := by
  have h := fastStrideSixIntervalScan_spec 893386797 895483949 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 895483949 897581101 = 6519 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 895483949 897581101).card = 6519 := by
  have h := fastStrideSixIntervalScan_spec 895483949 897581101 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 889192493 893386797).card = 13080 := by
  simpa using combineTwinPrimeSegments (by decide : 889192493 ≤ 891289645) (by decide : 891289645 ≤ 893386797) seg0 seg1

theorem join23 : (twinPrimeSegment 893386797 897581101).card = 13045 := by
  simpa using combineTwinPrimeSegments (by decide : 893386797 ≤ 895483949) (by decide : 895483949 ≤ 897581101) seg2 seg3

theorem total : (twinPrimeSegment 889192493 897581101).card = 26125 := by
  simpa using combineTwinPrimeSegments (by decide : 889192493 ≤ 893386797) (by decide : 893386797 ≤ 897581101) join01 join23

end
end B106
end Sude.FastTwinScan
