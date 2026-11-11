import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B116 (S464..S467). -/
namespace Sude.FastTwinScan
namespace B116
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 973078573 975175725 = 6396 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 973078573 975175725).card = 6396 := by
  have h := fastStrideSixIntervalScan_spec 973078573 975175725 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 975175725 977272877 = 6472 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 975175725 977272877).card = 6472 := by
  have h := fastStrideSixIntervalScan_spec 975175725 977272877 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 977272877 979370029 = 6414 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 977272877 979370029).card = 6414 := by
  have h := fastStrideSixIntervalScan_spec 977272877 979370029 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 979370029 981467181 = 6367 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 979370029 981467181).card = 6367 := by
  have h := fastStrideSixIntervalScan_spec 979370029 981467181 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 973078573 977272877).card = 12868 := by
  simpa using combineTwinPrimeSegments (by decide : 973078573 ≤ 975175725) (by decide : 975175725 ≤ 977272877) seg0 seg1

theorem join23 : (twinPrimeSegment 977272877 981467181).card = 12781 := by
  simpa using combineTwinPrimeSegments (by decide : 977272877 ≤ 979370029) (by decide : 979370029 ≤ 981467181) seg2 seg3

theorem total : (twinPrimeSegment 973078573 981467181).card = 25649 := by
  simpa using combineTwinPrimeSegments (by decide : 973078573 ≤ 977272877) (by decide : 977272877 ≤ 981467181) join01 join23

end
end B116
end Sude.FastTwinScan
