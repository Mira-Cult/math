import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B35 (S140..S143). -/
namespace Sude.FastTwinScan
namespace B35
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 293601325 295698477 = 7345 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 293601325 295698477).card = 7345 := by
  have h := fastStrideSixIntervalScan_spec 293601325 295698477 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 295698477 297795629 = 7223 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 295698477 297795629).card = 7223 := by
  have h := fastStrideSixIntervalScan_spec 295698477 297795629 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 297795629 299892781 = 7189 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 297795629 299892781).card = 7189 := by
  have h := fastStrideSixIntervalScan_spec 297795629 299892781 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 299892781 301989933 = 7226 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 299892781 301989933).card = 7226 := by
  have h := fastStrideSixIntervalScan_spec 299892781 301989933 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 293601325 297795629).card = 14568 := by
  simpa using combineTwinPrimeSegments (by decide : 293601325 ≤ 295698477) (by decide : 295698477 ≤ 297795629) seg0 seg1

theorem join23 : (twinPrimeSegment 297795629 301989933).card = 14415 := by
  simpa using combineTwinPrimeSegments (by decide : 297795629 ≤ 299892781) (by decide : 299892781 ≤ 301989933) seg2 seg3

theorem total : (twinPrimeSegment 293601325 301989933).card = 28983 := by
  simpa using combineTwinPrimeSegments (by decide : 293601325 ≤ 297795629) (by decide : 297795629 ≤ 301989933) join01 join23

end
end B35
end Sude.FastTwinScan
