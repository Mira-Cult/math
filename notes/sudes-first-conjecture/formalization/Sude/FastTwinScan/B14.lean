import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B14 (S056..S059). -/
namespace Sude.FastTwinScan
namespace B14
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 117440557 119537709 = 7961 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 117440557 119537709).card = 7961 := by
  have h := fastStrideSixIntervalScan_spec 117440557 119537709 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 119537709 121634861 = 7913 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 119537709 121634861).card = 7913 := by
  have h := fastStrideSixIntervalScan_spec 119537709 121634861 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 121634861 123732013 = 8008 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 121634861 123732013).card = 8008 := by
  have h := fastStrideSixIntervalScan_spec 121634861 123732013 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 123732013 125829165 = 7948 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 123732013 125829165).card = 7948 := by
  have h := fastStrideSixIntervalScan_spec 123732013 125829165 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 117440557 121634861).card = 15874 := by
  simpa using combineTwinPrimeSegments (by decide : 117440557 ≤ 119537709) (by decide : 119537709 ≤ 121634861) seg0 seg1

theorem join23 : (twinPrimeSegment 121634861 125829165).card = 15956 := by
  simpa using combineTwinPrimeSegments (by decide : 121634861 ≤ 123732013) (by decide : 123732013 ≤ 125829165) seg2 seg3

theorem total : (twinPrimeSegment 117440557 125829165).card = 31830 := by
  simpa using combineTwinPrimeSegments (by decide : 117440557 ≤ 121634861) (by decide : 121634861 ≤ 125829165) join01 join23

end
end B14
end Sude.FastTwinScan
