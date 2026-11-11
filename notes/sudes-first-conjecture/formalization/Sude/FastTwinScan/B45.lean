import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B45 (S180..S183). -/
namespace Sude.FastTwinScan
namespace B45
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 377487405 379584557 = 7044 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 377487405 379584557).card = 7044 := by
  have h := fastStrideSixIntervalScan_spec 377487405 379584557 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 379584557 381681709 = 7221 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 379584557 381681709).card = 7221 := by
  have h := fastStrideSixIntervalScan_spec 379584557 381681709 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 381681709 383778861 = 7199 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 381681709 383778861).card = 7199 := by
  have h := fastStrideSixIntervalScan_spec 381681709 383778861 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 383778861 385876013 = 7056 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 383778861 385876013).card = 7056 := by
  have h := fastStrideSixIntervalScan_spec 383778861 385876013 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 377487405 381681709).card = 14265 := by
  simpa using combineTwinPrimeSegments (by decide : 377487405 ≤ 379584557) (by decide : 379584557 ≤ 381681709) seg0 seg1

theorem join23 : (twinPrimeSegment 381681709 385876013).card = 14255 := by
  simpa using combineTwinPrimeSegments (by decide : 381681709 ≤ 383778861) (by decide : 383778861 ≤ 385876013) seg2 seg3

theorem total : (twinPrimeSegment 377487405 385876013).card = 28520 := by
  simpa using combineTwinPrimeSegments (by decide : 377487405 ≤ 381681709) (by decide : 381681709 ≤ 385876013) join01 join23

end
end B45
end Sude.FastTwinScan
