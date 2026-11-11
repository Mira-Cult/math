import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B22 (S088..S091). -/
namespace Sude.FastTwinScan
namespace B22
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 184549421 186646573 = 7649 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 184549421 186646573).card = 7649 := by
  have h := fastStrideSixIntervalScan_spec 184549421 186646573 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 186646573 188743725 = 7702 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 186646573 188743725).card = 7702 := by
  have h := fastStrideSixIntervalScan_spec 186646573 188743725 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 188743725 190840877 = 7586 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 188743725 190840877).card = 7586 := by
  have h := fastStrideSixIntervalScan_spec 188743725 190840877 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 190840877 192938029 = 7575 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 190840877 192938029).card = 7575 := by
  have h := fastStrideSixIntervalScan_spec 190840877 192938029 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 184549421 188743725).card = 15351 := by
  simpa using combineTwinPrimeSegments (by decide : 184549421 ≤ 186646573) (by decide : 186646573 ≤ 188743725) seg0 seg1

theorem join23 : (twinPrimeSegment 188743725 192938029).card = 15161 := by
  simpa using combineTwinPrimeSegments (by decide : 188743725 ≤ 190840877) (by decide : 190840877 ≤ 192938029) seg2 seg3

theorem total : (twinPrimeSegment 184549421 192938029).card = 30512 := by
  simpa using combineTwinPrimeSegments (by decide : 184549421 ≤ 188743725) (by decide : 188743725 ≤ 192938029) join01 join23

end
end B22
end Sude.FastTwinScan
