import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B36 (S144..S147). -/
namespace Sude.FastTwinScan
namespace B36
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 301989933 304087085 = 7203 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 301989933 304087085).card = 7203 := by
  have h := fastStrideSixIntervalScan_spec 301989933 304087085 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 304087085 306184237 = 7389 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 304087085 306184237).card = 7389 := by
  have h := fastStrideSixIntervalScan_spec 304087085 306184237 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 306184237 308281389 = 7342 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 306184237 308281389).card = 7342 := by
  have h := fastStrideSixIntervalScan_spec 306184237 308281389 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 308281389 310378541 = 7212 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 308281389 310378541).card = 7212 := by
  have h := fastStrideSixIntervalScan_spec 308281389 310378541 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 301989933 306184237).card = 14592 := by
  simpa using combineTwinPrimeSegments (by decide : 301989933 ≤ 304087085) (by decide : 304087085 ≤ 306184237) seg0 seg1

theorem join23 : (twinPrimeSegment 306184237 310378541).card = 14554 := by
  simpa using combineTwinPrimeSegments (by decide : 306184237 ≤ 308281389) (by decide : 308281389 ≤ 310378541) seg2 seg3

theorem total : (twinPrimeSegment 301989933 310378541).card = 29146 := by
  simpa using combineTwinPrimeSegments (by decide : 301989933 ≤ 306184237) (by decide : 306184237 ≤ 310378541) join01 join23

end
end B36
end Sude.FastTwinScan
