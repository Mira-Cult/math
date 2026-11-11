import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B110 (S440..S443). -/
namespace Sude.FastTwinScan
namespace B110
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 922746925 924844077 = 6437 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 922746925 924844077).card = 6437 := by
  have h := fastStrideSixIntervalScan_spec 922746925 924844077 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 924844077 926941229 = 6478 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 924844077 926941229).card = 6478 := by
  have h := fastStrideSixIntervalScan_spec 924844077 926941229 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 926941229 929038381 = 6441 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 926941229 929038381).card = 6441 := by
  have h := fastStrideSixIntervalScan_spec 926941229 929038381 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 929038381 931135533 = 6450 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 929038381 931135533).card = 6450 := by
  have h := fastStrideSixIntervalScan_spec 929038381 931135533 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 922746925 926941229).card = 12915 := by
  simpa using combineTwinPrimeSegments (by decide : 922746925 ≤ 924844077) (by decide : 924844077 ≤ 926941229) seg0 seg1

theorem join23 : (twinPrimeSegment 926941229 931135533).card = 12891 := by
  simpa using combineTwinPrimeSegments (by decide : 926941229 ≤ 929038381) (by decide : 929038381 ≤ 931135533) seg2 seg3

theorem total : (twinPrimeSegment 922746925 931135533).card = 25806 := by
  simpa using combineTwinPrimeSegments (by decide : 922746925 ≤ 926941229) (by decide : 926941229 ≤ 931135533) join01 join23

end
end B110
end Sude.FastTwinScan
