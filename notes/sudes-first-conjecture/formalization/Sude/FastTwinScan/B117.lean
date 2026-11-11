import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B117 (S468..S471). -/
namespace Sude.FastTwinScan
namespace B117
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 981467181 983564333 = 6506 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 981467181 983564333).card = 6506 := by
  have h := fastStrideSixIntervalScan_spec 981467181 983564333 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 983564333 985661485 = 6444 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 983564333 985661485).card = 6444 := by
  have h := fastStrideSixIntervalScan_spec 983564333 985661485 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 985661485 987758637 = 6496 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 985661485 987758637).card = 6496 := by
  have h := fastStrideSixIntervalScan_spec 985661485 987758637 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 987758637 989855789 = 6444 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 987758637 989855789).card = 6444 := by
  have h := fastStrideSixIntervalScan_spec 987758637 989855789 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 981467181 985661485).card = 12950 := by
  simpa using combineTwinPrimeSegments (by decide : 981467181 ≤ 983564333) (by decide : 983564333 ≤ 985661485) seg0 seg1

theorem join23 : (twinPrimeSegment 985661485 989855789).card = 12940 := by
  simpa using combineTwinPrimeSegments (by decide : 985661485 ≤ 987758637) (by decide : 987758637 ≤ 989855789) seg2 seg3

theorem total : (twinPrimeSegment 981467181 989855789).card = 25890 := by
  simpa using combineTwinPrimeSegments (by decide : 981467181 ≤ 985661485) (by decide : 985661485 ≤ 989855789) join01 join23

end
end B117
end Sude.FastTwinScan
