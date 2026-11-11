import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B13 (S052..S055). -/
namespace Sude.FastTwinScan
namespace B13
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 109051949 111149101 = 8121 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 109051949 111149101).card = 8121 := by
  have h := fastStrideSixIntervalScan_spec 109051949 111149101 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 111149101 113246253 = 7984 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 111149101 113246253).card = 7984 := by
  have h := fastStrideSixIntervalScan_spec 111149101 113246253 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 113246253 115343405 = 8057 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 113246253 115343405).card = 8057 := by
  have h := fastStrideSixIntervalScan_spec 113246253 115343405 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 115343405 117440557 = 8024 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 115343405 117440557).card = 8024 := by
  have h := fastStrideSixIntervalScan_spec 115343405 117440557 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 109051949 113246253).card = 16105 := by
  simpa using combineTwinPrimeSegments (by decide : 109051949 ≤ 111149101) (by decide : 111149101 ≤ 113246253) seg0 seg1

theorem join23 : (twinPrimeSegment 113246253 117440557).card = 16081 := by
  simpa using combineTwinPrimeSegments (by decide : 113246253 ≤ 115343405) (by decide : 115343405 ≤ 117440557) seg2 seg3

theorem total : (twinPrimeSegment 109051949 117440557).card = 32186 := by
  simpa using combineTwinPrimeSegments (by decide : 109051949 ≤ 113246253) (by decide : 113246253 ≤ 117440557) join01 join23

end
end B13
end Sude.FastTwinScan
