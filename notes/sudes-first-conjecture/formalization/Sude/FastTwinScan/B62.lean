import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B62 (S248..S251). -/
namespace Sude.FastTwinScan
namespace B62
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 520093741 522190893 = 6824 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 520093741 522190893).card = 6824 := by
  have h := fastStrideSixIntervalScan_spec 520093741 522190893 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 522190893 524288045 = 6851 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 522190893 524288045).card = 6851 := by
  have h := fastStrideSixIntervalScan_spec 522190893 524288045 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 524288045 526385197 = 6929 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 524288045 526385197).card = 6929 := by
  have h := fastStrideSixIntervalScan_spec 524288045 526385197 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 526385197 528482349 = 6947 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 526385197 528482349).card = 6947 := by
  have h := fastStrideSixIntervalScan_spec 526385197 528482349 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 520093741 524288045).card = 13675 := by
  simpa using combineTwinPrimeSegments (by decide : 520093741 ≤ 522190893) (by decide : 522190893 ≤ 524288045) seg0 seg1

theorem join23 : (twinPrimeSegment 524288045 528482349).card = 13876 := by
  simpa using combineTwinPrimeSegments (by decide : 524288045 ≤ 526385197) (by decide : 526385197 ≤ 528482349) seg2 seg3

theorem total : (twinPrimeSegment 520093741 528482349).card = 27551 := by
  simpa using combineTwinPrimeSegments (by decide : 520093741 ≤ 524288045) (by decide : 524288045 ≤ 528482349) join01 join23

end
end B62
end Sude.FastTwinScan
