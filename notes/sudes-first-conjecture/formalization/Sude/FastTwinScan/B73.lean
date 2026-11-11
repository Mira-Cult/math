import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B73 (S292..S295). -/
namespace Sude.FastTwinScan
namespace B73
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 612368429 614465581 = 6749 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 612368429 614465581).card = 6749 := by
  have h := fastStrideSixIntervalScan_spec 612368429 614465581 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 614465581 616562733 = 6868 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 614465581 616562733).card = 6868 := by
  have h := fastStrideSixIntervalScan_spec 614465581 616562733 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 616562733 618659885 = 6833 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 616562733 618659885).card = 6833 := by
  have h := fastStrideSixIntervalScan_spec 616562733 618659885 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 618659885 620757037 = 6689 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 618659885 620757037).card = 6689 := by
  have h := fastStrideSixIntervalScan_spec 618659885 620757037 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 612368429 616562733).card = 13617 := by
  simpa using combineTwinPrimeSegments (by decide : 612368429 ≤ 614465581) (by decide : 614465581 ≤ 616562733) seg0 seg1

theorem join23 : (twinPrimeSegment 616562733 620757037).card = 13522 := by
  simpa using combineTwinPrimeSegments (by decide : 616562733 ≤ 618659885) (by decide : 618659885 ≤ 620757037) seg2 seg3

theorem total : (twinPrimeSegment 612368429 620757037).card = 27139 := by
  simpa using combineTwinPrimeSegments (by decide : 612368429 ≤ 616562733) (by decide : 616562733 ≤ 620757037) join01 join23

end
end B73
end Sude.FastTwinScan
