import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B46 (S184..S187). -/
namespace Sude.FastTwinScan
namespace B46
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 385876013 387973165 = 7089 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 385876013 387973165).card = 7089 := by
  have h := fastStrideSixIntervalScan_spec 385876013 387973165 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 387973165 390070317 = 7002 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 387973165 390070317).card = 7002 := by
  have h := fastStrideSixIntervalScan_spec 387973165 390070317 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 390070317 392167469 = 7071 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 390070317 392167469).card = 7071 := by
  have h := fastStrideSixIntervalScan_spec 390070317 392167469 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 392167469 394264621 = 7056 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 392167469 394264621).card = 7056 := by
  have h := fastStrideSixIntervalScan_spec 392167469 394264621 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 385876013 390070317).card = 14091 := by
  simpa using combineTwinPrimeSegments (by decide : 385876013 ≤ 387973165) (by decide : 387973165 ≤ 390070317) seg0 seg1

theorem join23 : (twinPrimeSegment 390070317 394264621).card = 14127 := by
  simpa using combineTwinPrimeSegments (by decide : 390070317 ≤ 392167469) (by decide : 392167469 ≤ 394264621) seg2 seg3

theorem total : (twinPrimeSegment 385876013 394264621).card = 28218 := by
  simpa using combineTwinPrimeSegments (by decide : 385876013 ≤ 390070317) (by decide : 390070317 ≤ 394264621) join01 join23

end
end B46
end Sude.FastTwinScan
