import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B27 (S108..S111). -/
namespace Sude.FastTwinScan
namespace B27
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 226492461 228589613 = 7361 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 226492461 228589613).card = 7361 := by
  have h := fastStrideSixIntervalScan_spec 226492461 228589613 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 228589613 230686765 = 7445 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 228589613 230686765).card = 7445 := by
  have h := fastStrideSixIntervalScan_spec 228589613 230686765 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 230686765 232783917 = 7342 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 230686765 232783917).card = 7342 := by
  have h := fastStrideSixIntervalScan_spec 230686765 232783917 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 232783917 234881069 = 7437 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 232783917 234881069).card = 7437 := by
  have h := fastStrideSixIntervalScan_spec 232783917 234881069 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 226492461 230686765).card = 14806 := by
  simpa using combineTwinPrimeSegments (by decide : 226492461 ≤ 228589613) (by decide : 228589613 ≤ 230686765) seg0 seg1

theorem join23 : (twinPrimeSegment 230686765 234881069).card = 14779 := by
  simpa using combineTwinPrimeSegments (by decide : 230686765 ≤ 232783917) (by decide : 232783917 ≤ 234881069) seg2 seg3

theorem total : (twinPrimeSegment 226492461 234881069).card = 29585 := by
  simpa using combineTwinPrimeSegments (by decide : 226492461 ≤ 230686765) (by decide : 230686765 ≤ 234881069) join01 join23

end
end B27
end Sude.FastTwinScan
