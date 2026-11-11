import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B69 (S276..S279). -/
namespace Sude.FastTwinScan
namespace B69
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 578813997 580911149 = 6755 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 578813997 580911149).card = 6755 := by
  have h := fastStrideSixIntervalScan_spec 578813997 580911149 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 580911149 583008301 = 6826 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 580911149 583008301).card = 6826 := by
  have h := fastStrideSixIntervalScan_spec 580911149 583008301 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 583008301 585105453 = 6769 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 583008301 585105453).card = 6769 := by
  have h := fastStrideSixIntervalScan_spec 583008301 585105453 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 585105453 587202605 = 6865 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 585105453 587202605).card = 6865 := by
  have h := fastStrideSixIntervalScan_spec 585105453 587202605 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 578813997 583008301).card = 13581 := by
  simpa using combineTwinPrimeSegments (by decide : 578813997 ≤ 580911149) (by decide : 580911149 ≤ 583008301) seg0 seg1

theorem join23 : (twinPrimeSegment 583008301 587202605).card = 13634 := by
  simpa using combineTwinPrimeSegments (by decide : 583008301 ≤ 585105453) (by decide : 585105453 ≤ 587202605) seg2 seg3

theorem total : (twinPrimeSegment 578813997 587202605).card = 27215 := by
  simpa using combineTwinPrimeSegments (by decide : 578813997 ≤ 583008301) (by decide : 583008301 ≤ 587202605) join01 join23

end
end B69
end Sude.FastTwinScan
