import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B57 (S228..S231). -/
namespace Sude.FastTwinScan
namespace B57
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 478150701 480247853 = 6960 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 478150701 480247853).card = 6960 := by
  have h := fastStrideSixIntervalScan_spec 478150701 480247853 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 480247853 482345005 = 6809 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 480247853 482345005).card = 6809 := by
  have h := fastStrideSixIntervalScan_spec 480247853 482345005 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 482345005 484442157 = 6910 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 482345005 484442157).card = 6910 := by
  have h := fastStrideSixIntervalScan_spec 482345005 484442157 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 484442157 486539309 = 6851 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 484442157 486539309).card = 6851 := by
  have h := fastStrideSixIntervalScan_spec 484442157 486539309 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 478150701 482345005).card = 13769 := by
  simpa using combineTwinPrimeSegments (by decide : 478150701 ≤ 480247853) (by decide : 480247853 ≤ 482345005) seg0 seg1

theorem join23 : (twinPrimeSegment 482345005 486539309).card = 13761 := by
  simpa using combineTwinPrimeSegments (by decide : 482345005 ≤ 484442157) (by decide : 484442157 ≤ 486539309) seg2 seg3

theorem total : (twinPrimeSegment 478150701 486539309).card = 27530 := by
  simpa using combineTwinPrimeSegments (by decide : 478150701 ≤ 482345005) (by decide : 482345005 ≤ 486539309) join01 join23

end
end B57
end Sude.FastTwinScan
