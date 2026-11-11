import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B16 (S064..S067). -/
namespace Sude.FastTwinScan
namespace B16
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 134217773 136314925 = 7919 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 134217773 136314925).card = 7919 := by
  have h := fastStrideSixIntervalScan_spec 134217773 136314925 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 136314925 138412077 = 7920 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 136314925 138412077).card = 7920 := by
  have h := fastStrideSixIntervalScan_spec 136314925 138412077 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 138412077 140509229 = 7895 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 138412077 140509229).card = 7895 := by
  have h := fastStrideSixIntervalScan_spec 138412077 140509229 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 140509229 142606381 = 7794 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 140509229 142606381).card = 7794 := by
  have h := fastStrideSixIntervalScan_spec 140509229 142606381 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 134217773 138412077).card = 15839 := by
  simpa using combineTwinPrimeSegments (by decide : 134217773 ≤ 136314925) (by decide : 136314925 ≤ 138412077) seg0 seg1

theorem join23 : (twinPrimeSegment 138412077 142606381).card = 15689 := by
  simpa using combineTwinPrimeSegments (by decide : 138412077 ≤ 140509229) (by decide : 140509229 ≤ 142606381) seg2 seg3

theorem total : (twinPrimeSegment 134217773 142606381).card = 31528 := by
  simpa using combineTwinPrimeSegments (by decide : 134217773 ≤ 138412077) (by decide : 138412077 ≤ 142606381) join01 join23

end
end B16
end Sude.FastTwinScan
