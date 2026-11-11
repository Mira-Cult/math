import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B89 (S356..S359). -/
namespace Sude.FastTwinScan
namespace B89
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 746586157 748683309 = 6548 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 746586157 748683309).card = 6548 := by
  have h := fastStrideSixIntervalScan_spec 746586157 748683309 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 748683309 750780461 = 6637 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 748683309 750780461).card = 6637 := by
  have h := fastStrideSixIntervalScan_spec 748683309 750780461 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 750780461 752877613 = 6628 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 750780461 752877613).card = 6628 := by
  have h := fastStrideSixIntervalScan_spec 750780461 752877613 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 752877613 754974765 = 6532 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 752877613 754974765).card = 6532 := by
  have h := fastStrideSixIntervalScan_spec 752877613 754974765 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 746586157 750780461).card = 13185 := by
  simpa using combineTwinPrimeSegments (by decide : 746586157 ≤ 748683309) (by decide : 748683309 ≤ 750780461) seg0 seg1

theorem join23 : (twinPrimeSegment 750780461 754974765).card = 13160 := by
  simpa using combineTwinPrimeSegments (by decide : 750780461 ≤ 752877613) (by decide : 752877613 ≤ 754974765) seg2 seg3

theorem total : (twinPrimeSegment 746586157 754974765).card = 26345 := by
  simpa using combineTwinPrimeSegments (by decide : 746586157 ≤ 750780461) (by decide : 750780461 ≤ 754974765) join01 join23

end
end B89
end Sude.FastTwinScan
