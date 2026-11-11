import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B75 (S300..S303). -/
namespace Sude.FastTwinScan
namespace B75
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 629145645 631242797 = 6756 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 629145645 631242797).card = 6756 := by
  have h := fastStrideSixIntervalScan_spec 629145645 631242797 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 631242797 633339949 = 6809 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 631242797 633339949).card = 6809 := by
  have h := fastStrideSixIntervalScan_spec 631242797 633339949 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 633339949 635437101 = 6592 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 633339949 635437101).card = 6592 := by
  have h := fastStrideSixIntervalScan_spec 633339949 635437101 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 635437101 637534253 = 6794 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 635437101 637534253).card = 6794 := by
  have h := fastStrideSixIntervalScan_spec 635437101 637534253 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 629145645 633339949).card = 13565 := by
  simpa using combineTwinPrimeSegments (by decide : 629145645 ≤ 631242797) (by decide : 631242797 ≤ 633339949) seg0 seg1

theorem join23 : (twinPrimeSegment 633339949 637534253).card = 13386 := by
  simpa using combineTwinPrimeSegments (by decide : 633339949 ≤ 635437101) (by decide : 635437101 ≤ 637534253) seg2 seg3

theorem total : (twinPrimeSegment 629145645 637534253).card = 26951 := by
  simpa using combineTwinPrimeSegments (by decide : 629145645 ≤ 633339949) (by decide : 633339949 ≤ 637534253) join01 join23

end
end B75
end Sude.FastTwinScan
