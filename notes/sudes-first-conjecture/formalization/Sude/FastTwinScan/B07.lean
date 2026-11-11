import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B07 (S028..S031). -/
namespace Sude.FastTwinScan
namespace B07
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 58720301 60817453 = 8616 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 58720301 60817453).card = 8616 := by
  have h := fastStrideSixIntervalScan_spec 58720301 60817453 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 60817453 62914605 = 8498 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 60817453 62914605).card = 8498 := by
  have h := fastStrideSixIntervalScan_spec 60817453 62914605 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 62914605 65011757 = 8602 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 62914605 65011757).card = 8602 := by
  have h := fastStrideSixIntervalScan_spec 62914605 65011757 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 65011757 67108909 = 8545 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 65011757 67108909).card = 8545 := by
  have h := fastStrideSixIntervalScan_spec 65011757 67108909 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 58720301 62914605).card = 17114 := by
  simpa using combineTwinPrimeSegments (by decide : 58720301 ≤ 60817453) (by decide : 60817453 ≤ 62914605) seg0 seg1

theorem join23 : (twinPrimeSegment 62914605 67108909).card = 17147 := by
  simpa using combineTwinPrimeSegments (by decide : 62914605 ≤ 65011757) (by decide : 65011757 ≤ 67108909) seg2 seg3

theorem total : (twinPrimeSegment 58720301 67108909).card = 34261 := by
  simpa using combineTwinPrimeSegments (by decide : 58720301 ≤ 62914605) (by decide : 62914605 ≤ 67108909) join01 join23

end
end B07
end Sude.FastTwinScan
