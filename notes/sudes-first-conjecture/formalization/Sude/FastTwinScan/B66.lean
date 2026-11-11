import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B66 (S264..S267). -/
namespace Sude.FastTwinScan
namespace B66
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 553648173 555745325 = 6765 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 553648173 555745325).card = 6765 := by
  have h := fastStrideSixIntervalScan_spec 553648173 555745325 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 555745325 557842477 = 6889 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 555745325 557842477).card = 6889 := by
  have h := fastStrideSixIntervalScan_spec 555745325 557842477 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 557842477 559939629 = 6834 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 557842477 559939629).card = 6834 := by
  have h := fastStrideSixIntervalScan_spec 557842477 559939629 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 559939629 562036781 = 6805 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 559939629 562036781).card = 6805 := by
  have h := fastStrideSixIntervalScan_spec 559939629 562036781 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 553648173 557842477).card = 13654 := by
  simpa using combineTwinPrimeSegments (by decide : 553648173 ≤ 555745325) (by decide : 555745325 ≤ 557842477) seg0 seg1

theorem join23 : (twinPrimeSegment 557842477 562036781).card = 13639 := by
  simpa using combineTwinPrimeSegments (by decide : 557842477 ≤ 559939629) (by decide : 559939629 ≤ 562036781) seg2 seg3

theorem total : (twinPrimeSegment 553648173 562036781).card = 27293 := by
  simpa using combineTwinPrimeSegments (by decide : 553648173 ≤ 557842477) (by decide : 557842477 ≤ 562036781) join01 join23

end
end B66
end Sude.FastTwinScan
