import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B91 (S364..S367). -/
namespace Sude.FastTwinScan
namespace B91
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 763363373 765460525 = 6508 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 763363373 765460525).card = 6508 := by
  have h := fastStrideSixIntervalScan_spec 763363373 765460525 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 765460525 767557677 = 6560 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 765460525 767557677).card = 6560 := by
  have h := fastStrideSixIntervalScan_spec 765460525 767557677 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 767557677 769654829 = 6640 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 767557677 769654829).card = 6640 := by
  have h := fastStrideSixIntervalScan_spec 767557677 769654829 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 769654829 771751981 = 6631 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 769654829 771751981).card = 6631 := by
  have h := fastStrideSixIntervalScan_spec 769654829 771751981 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 763363373 767557677).card = 13068 := by
  simpa using combineTwinPrimeSegments (by decide : 763363373 ≤ 765460525) (by decide : 765460525 ≤ 767557677) seg0 seg1

theorem join23 : (twinPrimeSegment 767557677 771751981).card = 13271 := by
  simpa using combineTwinPrimeSegments (by decide : 767557677 ≤ 769654829) (by decide : 769654829 ≤ 771751981) seg2 seg3

theorem total : (twinPrimeSegment 763363373 771751981).card = 26339 := by
  simpa using combineTwinPrimeSegments (by decide : 763363373 ≤ 767557677) (by decide : 767557677 ≤ 771751981) join01 join23

end
end B91
end Sude.FastTwinScan
