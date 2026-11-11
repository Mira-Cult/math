import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B63 (S252..S255). -/
namespace Sude.FastTwinScan
namespace B63
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 528482349 530579501 = 6854 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 528482349 530579501).card = 6854 := by
  have h := fastStrideSixIntervalScan_spec 528482349 530579501 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 530579501 532676653 = 6770 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 530579501 532676653).card = 6770 := by
  have h := fastStrideSixIntervalScan_spec 530579501 532676653 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 532676653 534773805 = 6915 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 532676653 534773805).card = 6915 := by
  have h := fastStrideSixIntervalScan_spec 532676653 534773805 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 534773805 536870957 = 6924 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 534773805 536870957).card = 6924 := by
  have h := fastStrideSixIntervalScan_spec 534773805 536870957 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 528482349 532676653).card = 13624 := by
  simpa using combineTwinPrimeSegments (by decide : 528482349 ≤ 530579501) (by decide : 530579501 ≤ 532676653) seg0 seg1

theorem join23 : (twinPrimeSegment 532676653 536870957).card = 13839 := by
  simpa using combineTwinPrimeSegments (by decide : 532676653 ≤ 534773805) (by decide : 534773805 ≤ 536870957) seg2 seg3

theorem total : (twinPrimeSegment 528482349 536870957).card = 27463 := by
  simpa using combineTwinPrimeSegments (by decide : 528482349 ≤ 532676653) (by decide : 532676653 ≤ 536870957) join01 join23

end
end B63
end Sude.FastTwinScan
