import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B78 (S312..S315). -/
namespace Sude.FastTwinScan
namespace B78
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 654311469 656408621 = 6720 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 654311469 656408621).card = 6720 := by
  have h := fastStrideSixIntervalScan_spec 654311469 656408621 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 656408621 658505773 = 6743 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 656408621 658505773).card = 6743 := by
  have h := fastStrideSixIntervalScan_spec 656408621 658505773 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 658505773 660602925 = 6681 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 658505773 660602925).card = 6681 := by
  have h := fastStrideSixIntervalScan_spec 658505773 660602925 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 660602925 662700077 = 6681 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 660602925 662700077).card = 6681 := by
  have h := fastStrideSixIntervalScan_spec 660602925 662700077 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 654311469 658505773).card = 13463 := by
  simpa using combineTwinPrimeSegments (by decide : 654311469 ≤ 656408621) (by decide : 656408621 ≤ 658505773) seg0 seg1

theorem join23 : (twinPrimeSegment 658505773 662700077).card = 13362 := by
  simpa using combineTwinPrimeSegments (by decide : 658505773 ≤ 660602925) (by decide : 660602925 ≤ 662700077) seg2 seg3

theorem total : (twinPrimeSegment 654311469 662700077).card = 26825 := by
  simpa using combineTwinPrimeSegments (by decide : 654311469 ≤ 658505773) (by decide : 658505773 ≤ 662700077) join01 join23

end
end B78
end Sude.FastTwinScan
