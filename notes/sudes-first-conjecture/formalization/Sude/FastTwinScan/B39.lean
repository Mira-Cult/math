import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B39 (S156..S159). -/
namespace Sude.FastTwinScan
namespace B39
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 327155757 329252909 = 7143 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 327155757 329252909).card = 7143 := by
  have h := fastStrideSixIntervalScan_spec 327155757 329252909 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 329252909 331350061 = 7164 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 329252909 331350061).card = 7164 := by
  have h := fastStrideSixIntervalScan_spec 329252909 331350061 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 331350061 333447213 = 7246 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 331350061 333447213).card = 7246 := by
  have h := fastStrideSixIntervalScan_spec 331350061 333447213 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 333447213 335544365 = 7207 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 333447213 335544365).card = 7207 := by
  have h := fastStrideSixIntervalScan_spec 333447213 335544365 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 327155757 331350061).card = 14307 := by
  simpa using combineTwinPrimeSegments (by decide : 327155757 ≤ 329252909) (by decide : 329252909 ≤ 331350061) seg0 seg1

theorem join23 : (twinPrimeSegment 331350061 335544365).card = 14453 := by
  simpa using combineTwinPrimeSegments (by decide : 331350061 ≤ 333447213) (by decide : 333447213 ≤ 335544365) seg2 seg3

theorem total : (twinPrimeSegment 327155757 335544365).card = 28760 := by
  simpa using combineTwinPrimeSegments (by decide : 327155757 ≤ 331350061) (by decide : 331350061 ≤ 335544365) join01 join23

end
end B39
end Sude.FastTwinScan
