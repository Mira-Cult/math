import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B127 (S508..S511). -/
namespace Sude.FastTwinScan
namespace B127
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 1065353261 1067450413 = 6553 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 1065353261 1067450413).card = 6553 := by
  have h := fastStrideSixIntervalScan_spec 1065353261 1067450413 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 1067450413 1069547565 = 6516 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 1067450413 1069547565).card = 6516 := by
  have h := fastStrideSixIntervalScan_spec 1067450413 1069547565 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 1069547565 1071644717 = 6379 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 1069547565 1071644717).card = 6379 := by
  have h := fastStrideSixIntervalScan_spec 1069547565 1071644717 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 1071644717 1073741823 = 6444 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 1071644717 1073741823).card = 6444 := by
  have h := fastStrideSixIntervalScan_spec 1071644717 1073741823 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 1065353261 1069547565).card = 13069 := by
  simpa using combineTwinPrimeSegments (by decide : 1065353261 ≤ 1067450413) (by decide : 1067450413 ≤ 1069547565) seg0 seg1

theorem join23 : (twinPrimeSegment 1069547565 1073741823).card = 12823 := by
  simpa using combineTwinPrimeSegments (by decide : 1069547565 ≤ 1071644717) (by decide : 1071644717 ≤ 1073741823) seg2 seg3

theorem total : (twinPrimeSegment 1065353261 1073741823).card = 25892 := by
  simpa using combineTwinPrimeSegments (by decide : 1065353261 ≤ 1069547565) (by decide : 1069547565 ≤ 1073741823) join01 join23

end
end B127
end Sude.FastTwinScan
