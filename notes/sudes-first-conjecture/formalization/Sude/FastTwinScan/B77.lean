import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B77 (S308..S311). -/
namespace Sude.FastTwinScan
namespace B77
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 645922861 648020013 = 6791 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 645922861 648020013).card = 6791 := by
  have h := fastStrideSixIntervalScan_spec 645922861 648020013 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 648020013 650117165 = 6719 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 648020013 650117165).card = 6719 := by
  have h := fastStrideSixIntervalScan_spec 648020013 650117165 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 650117165 652214317 = 6731 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 650117165 652214317).card = 6731 := by
  have h := fastStrideSixIntervalScan_spec 650117165 652214317 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 652214317 654311469 = 6753 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 652214317 654311469).card = 6753 := by
  have h := fastStrideSixIntervalScan_spec 652214317 654311469 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 645922861 650117165).card = 13510 := by
  simpa using combineTwinPrimeSegments (by decide : 645922861 ≤ 648020013) (by decide : 648020013 ≤ 650117165) seg0 seg1

theorem join23 : (twinPrimeSegment 650117165 654311469).card = 13484 := by
  simpa using combineTwinPrimeSegments (by decide : 650117165 ≤ 652214317) (by decide : 652214317 ≤ 654311469) seg2 seg3

theorem total : (twinPrimeSegment 645922861 654311469).card = 26994 := by
  simpa using combineTwinPrimeSegments (by decide : 645922861 ≤ 650117165) (by decide : 650117165 ≤ 654311469) join01 join23

end
end B77
end Sude.FastTwinScan
