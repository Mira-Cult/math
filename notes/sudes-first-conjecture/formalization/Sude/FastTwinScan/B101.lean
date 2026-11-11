import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B101 (S404..S407). -/
namespace Sude.FastTwinScan
namespace B101
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 847249453 849346605 = 6534 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 847249453 849346605).card = 6534 := by
  have h := fastStrideSixIntervalScan_spec 847249453 849346605 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 849346605 851443757 = 6626 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 849346605 851443757).card = 6626 := by
  have h := fastStrideSixIntervalScan_spec 849346605 851443757 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 851443757 853540909 = 6567 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 851443757 853540909).card = 6567 := by
  have h := fastStrideSixIntervalScan_spec 851443757 853540909 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 853540909 855638061 = 6568 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 853540909 855638061).card = 6568 := by
  have h := fastStrideSixIntervalScan_spec 853540909 855638061 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 847249453 851443757).card = 13160 := by
  simpa using combineTwinPrimeSegments (by decide : 847249453 ≤ 849346605) (by decide : 849346605 ≤ 851443757) seg0 seg1

theorem join23 : (twinPrimeSegment 851443757 855638061).card = 13135 := by
  simpa using combineTwinPrimeSegments (by decide : 851443757 ≤ 853540909) (by decide : 853540909 ≤ 855638061) seg2 seg3

theorem total : (twinPrimeSegment 847249453 855638061).card = 26295 := by
  simpa using combineTwinPrimeSegments (by decide : 847249453 ≤ 851443757) (by decide : 851443757 ≤ 855638061) join01 join23

end
end B101
end Sude.FastTwinScan
