import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B111 (S444..S447). -/
namespace Sude.FastTwinScan
namespace B111
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 931135533 933232685 = 6541 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 931135533 933232685).card = 6541 := by
  have h := fastStrideSixIntervalScan_spec 931135533 933232685 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 933232685 935329837 = 6591 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 933232685 935329837).card = 6591 := by
  have h := fastStrideSixIntervalScan_spec 933232685 935329837 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 935329837 937426989 = 6550 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 935329837 937426989).card = 6550 := by
  have h := fastStrideSixIntervalScan_spec 935329837 937426989 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 937426989 939524141 = 6505 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 937426989 939524141).card = 6505 := by
  have h := fastStrideSixIntervalScan_spec 937426989 939524141 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 931135533 935329837).card = 13132 := by
  simpa using combineTwinPrimeSegments (by decide : 931135533 ≤ 933232685) (by decide : 933232685 ≤ 935329837) seg0 seg1

theorem join23 : (twinPrimeSegment 935329837 939524141).card = 13055 := by
  simpa using combineTwinPrimeSegments (by decide : 935329837 ≤ 937426989) (by decide : 937426989 ≤ 939524141) seg2 seg3

theorem total : (twinPrimeSegment 931135533 939524141).card = 26187 := by
  simpa using combineTwinPrimeSegments (by decide : 931135533 ≤ 935329837) (by decide : 935329837 ≤ 939524141) join01 join23

end
end B111
end Sude.FastTwinScan
