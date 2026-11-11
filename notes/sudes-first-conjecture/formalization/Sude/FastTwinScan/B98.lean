import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B98 (S392..S395). -/
namespace Sude.FastTwinScan
namespace B98
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 822083629 824180781 = 6571 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 822083629 824180781).card = 6571 := by
  have h := fastStrideSixIntervalScan_spec 822083629 824180781 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 824180781 826277933 = 6546 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 824180781 826277933).card = 6546 := by
  have h := fastStrideSixIntervalScan_spec 824180781 826277933 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 826277933 828375085 = 6637 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 826277933 828375085).card = 6637 := by
  have h := fastStrideSixIntervalScan_spec 826277933 828375085 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 828375085 830472237 = 6491 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 828375085 830472237).card = 6491 := by
  have h := fastStrideSixIntervalScan_spec 828375085 830472237 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 822083629 826277933).card = 13117 := by
  simpa using combineTwinPrimeSegments (by decide : 822083629 ≤ 824180781) (by decide : 824180781 ≤ 826277933) seg0 seg1

theorem join23 : (twinPrimeSegment 826277933 830472237).card = 13128 := by
  simpa using combineTwinPrimeSegments (by decide : 826277933 ≤ 828375085) (by decide : 828375085 ≤ 830472237) seg2 seg3

theorem total : (twinPrimeSegment 822083629 830472237).card = 26245 := by
  simpa using combineTwinPrimeSegments (by decide : 822083629 ≤ 826277933) (by decide : 826277933 ≤ 830472237) join01 join23

end
end B98
end Sude.FastTwinScan
