import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B76 (S304..S307). -/
namespace Sude.FastTwinScan
namespace B76
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 637534253 639631405 = 6668 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 637534253 639631405).card = 6668 := by
  have h := fastStrideSixIntervalScan_spec 637534253 639631405 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 639631405 641728557 = 6776 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 639631405 641728557).card = 6776 := by
  have h := fastStrideSixIntervalScan_spec 639631405 641728557 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 641728557 643825709 = 6580 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 641728557 643825709).card = 6580 := by
  have h := fastStrideSixIntervalScan_spec 641728557 643825709 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 643825709 645922861 = 6646 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 643825709 645922861).card = 6646 := by
  have h := fastStrideSixIntervalScan_spec 643825709 645922861 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 637534253 641728557).card = 13444 := by
  simpa using combineTwinPrimeSegments (by decide : 637534253 ≤ 639631405) (by decide : 639631405 ≤ 641728557) seg0 seg1

theorem join23 : (twinPrimeSegment 641728557 645922861).card = 13226 := by
  simpa using combineTwinPrimeSegments (by decide : 641728557 ≤ 643825709) (by decide : 643825709 ≤ 645922861) seg2 seg3

theorem total : (twinPrimeSegment 637534253 645922861).card = 26670 := by
  simpa using combineTwinPrimeSegments (by decide : 637534253 ≤ 641728557) (by decide : 641728557 ≤ 645922861) join01 join23

end
end B76
end Sude.FastTwinScan
