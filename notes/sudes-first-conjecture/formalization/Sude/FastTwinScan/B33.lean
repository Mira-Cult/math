import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B33 (S132..S135). -/
namespace Sude.FastTwinScan
namespace B33
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 276824109 278921261 = 7324 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 276824109 278921261).card = 7324 := by
  have h := fastStrideSixIntervalScan_spec 276824109 278921261 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 278921261 281018413 = 7431 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 278921261 281018413).card = 7431 := by
  have h := fastStrideSixIntervalScan_spec 278921261 281018413 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 281018413 283115565 = 7333 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 281018413 283115565).card = 7333 := by
  have h := fastStrideSixIntervalScan_spec 281018413 283115565 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 283115565 285212717 = 7312 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 283115565 285212717).card = 7312 := by
  have h := fastStrideSixIntervalScan_spec 283115565 285212717 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 276824109 281018413).card = 14755 := by
  simpa using combineTwinPrimeSegments (by decide : 276824109 ≤ 278921261) (by decide : 278921261 ≤ 281018413) seg0 seg1

theorem join23 : (twinPrimeSegment 281018413 285212717).card = 14645 := by
  simpa using combineTwinPrimeSegments (by decide : 281018413 ≤ 283115565) (by decide : 283115565 ≤ 285212717) seg2 seg3

theorem total : (twinPrimeSegment 276824109 285212717).card = 29400 := by
  simpa using combineTwinPrimeSegments (by decide : 276824109 ≤ 281018413) (by decide : 281018413 ≤ 285212717) join01 join23

end
end B33
end Sude.FastTwinScan
