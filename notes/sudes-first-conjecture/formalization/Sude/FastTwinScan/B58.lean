import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B58 (S232..S235). -/
namespace Sude.FastTwinScan
namespace B58
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 486539309 488636461 = 6876 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 486539309 488636461).card = 6876 := by
  have h := fastStrideSixIntervalScan_spec 486539309 488636461 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 488636461 490733613 = 6886 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 488636461 490733613).card = 6886 := by
  have h := fastStrideSixIntervalScan_spec 488636461 490733613 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 490733613 492830765 = 6938 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 490733613 492830765).card = 6938 := by
  have h := fastStrideSixIntervalScan_spec 490733613 492830765 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 492830765 494927917 = 6838 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 492830765 494927917).card = 6838 := by
  have h := fastStrideSixIntervalScan_spec 492830765 494927917 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 486539309 490733613).card = 13762 := by
  simpa using combineTwinPrimeSegments (by decide : 486539309 ≤ 488636461) (by decide : 488636461 ≤ 490733613) seg0 seg1

theorem join23 : (twinPrimeSegment 490733613 494927917).card = 13776 := by
  simpa using combineTwinPrimeSegments (by decide : 490733613 ≤ 492830765) (by decide : 492830765 ≤ 494927917) seg2 seg3

theorem total : (twinPrimeSegment 486539309 494927917).card = 27538 := by
  simpa using combineTwinPrimeSegments (by decide : 486539309 ≤ 490733613) (by decide : 490733613 ≤ 494927917) join01 join23

end
end B58
end Sude.FastTwinScan
