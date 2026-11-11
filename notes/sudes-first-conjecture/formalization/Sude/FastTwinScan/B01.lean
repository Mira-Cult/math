import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B01 (S004..S007). -/
namespace Sude.FastTwinScan
namespace B01
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 8388653 10485805 = 10823 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 8388653 10485805).card = 10823 := by
  have h := fastStrideSixIntervalScan_spec 8388653 10485805 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 10485805 12582957 = 10410 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 10485805 12582957).card = 10410 := by
  have h := fastStrideSixIntervalScan_spec 10485805 12582957 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 12582957 14680109 = 10231 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 12582957 14680109).card = 10231 := by
  have h := fastStrideSixIntervalScan_spec 12582957 14680109 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 14680109 16777261 = 10143 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 14680109 16777261).card = 10143 := by
  have h := fastStrideSixIntervalScan_spec 14680109 16777261 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 8388653 12582957).card = 21233 := by
  simpa using combineTwinPrimeSegments (by decide : 8388653 ≤ 10485805) (by decide : 10485805 ≤ 12582957) seg0 seg1

theorem join23 : (twinPrimeSegment 12582957 16777261).card = 20374 := by
  simpa using combineTwinPrimeSegments (by decide : 12582957 ≤ 14680109) (by decide : 14680109 ≤ 16777261) seg2 seg3

theorem total : (twinPrimeSegment 8388653 16777261).card = 41607 := by
  simpa using combineTwinPrimeSegments (by decide : 8388653 ≤ 12582957) (by decide : 12582957 ≤ 16777261) join01 join23

end
end B01
end Sude.FastTwinScan
