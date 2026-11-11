import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B96 (S384..S387). -/
namespace Sude.FastTwinScan
namespace B96
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 805306413 807403565 = 6629 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 805306413 807403565).card = 6629 := by
  have h := fastStrideSixIntervalScan_spec 805306413 807403565 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 807403565 809500717 = 6513 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 807403565 809500717).card = 6513 := by
  have h := fastStrideSixIntervalScan_spec 807403565 809500717 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 809500717 811597869 = 6592 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 809500717 811597869).card = 6592 := by
  have h := fastStrideSixIntervalScan_spec 809500717 811597869 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 811597869 813695021 = 6584 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 811597869 813695021).card = 6584 := by
  have h := fastStrideSixIntervalScan_spec 811597869 813695021 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 805306413 809500717).card = 13142 := by
  simpa using combineTwinPrimeSegments (by decide : 805306413 ≤ 807403565) (by decide : 807403565 ≤ 809500717) seg0 seg1

theorem join23 : (twinPrimeSegment 809500717 813695021).card = 13176 := by
  simpa using combineTwinPrimeSegments (by decide : 809500717 ≤ 811597869) (by decide : 811597869 ≤ 813695021) seg2 seg3

theorem total : (twinPrimeSegment 805306413 813695021).card = 26318 := by
  simpa using combineTwinPrimeSegments (by decide : 805306413 ≤ 809500717) (by decide : 809500717 ≤ 813695021) join01 join23

end
end B96
end Sude.FastTwinScan
