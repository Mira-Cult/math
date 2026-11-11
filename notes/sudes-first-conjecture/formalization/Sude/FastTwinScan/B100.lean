import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B100 (S400..S403). -/
namespace Sude.FastTwinScan
namespace B100
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 838860845 840957997 = 6571 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 838860845 840957997).card = 6571 := by
  have h := fastStrideSixIntervalScan_spec 838860845 840957997 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 840957997 843055149 = 6562 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 840957997 843055149).card = 6562 := by
  have h := fastStrideSixIntervalScan_spec 840957997 843055149 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 843055149 845152301 = 6504 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 843055149 845152301).card = 6504 := by
  have h := fastStrideSixIntervalScan_spec 843055149 845152301 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 845152301 847249453 = 6476 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 845152301 847249453).card = 6476 := by
  have h := fastStrideSixIntervalScan_spec 845152301 847249453 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 838860845 843055149).card = 13133 := by
  simpa using combineTwinPrimeSegments (by decide : 838860845 ≤ 840957997) (by decide : 840957997 ≤ 843055149) seg0 seg1

theorem join23 : (twinPrimeSegment 843055149 847249453).card = 12980 := by
  simpa using combineTwinPrimeSegments (by decide : 843055149 ≤ 845152301) (by decide : 845152301 ≤ 847249453) seg2 seg3

theorem total : (twinPrimeSegment 838860845 847249453).card = 26113 := by
  simpa using combineTwinPrimeSegments (by decide : 838860845 ≤ 843055149) (by decide : 843055149 ≤ 847249453) join01 join23

end
end B100
end Sude.FastTwinScan
