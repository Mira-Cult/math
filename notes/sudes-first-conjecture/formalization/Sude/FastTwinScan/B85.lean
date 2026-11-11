import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B85 (S340..S343). -/
namespace Sude.FastTwinScan
namespace B85
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 713031725 715128877 = 6656 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 713031725 715128877).card = 6656 := by
  have h := fastStrideSixIntervalScan_spec 713031725 715128877 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 715128877 717226029 = 6644 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 715128877 717226029).card = 6644 := by
  have h := fastStrideSixIntervalScan_spec 715128877 717226029 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 717226029 719323181 = 6689 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 717226029 719323181).card = 6689 := by
  have h := fastStrideSixIntervalScan_spec 717226029 719323181 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 719323181 721420333 = 6590 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 719323181 721420333).card = 6590 := by
  have h := fastStrideSixIntervalScan_spec 719323181 721420333 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 713031725 717226029).card = 13300 := by
  simpa using combineTwinPrimeSegments (by decide : 713031725 ≤ 715128877) (by decide : 715128877 ≤ 717226029) seg0 seg1

theorem join23 : (twinPrimeSegment 717226029 721420333).card = 13279 := by
  simpa using combineTwinPrimeSegments (by decide : 717226029 ≤ 719323181) (by decide : 719323181 ≤ 721420333) seg2 seg3

theorem total : (twinPrimeSegment 713031725 721420333).card = 26579 := by
  simpa using combineTwinPrimeSegments (by decide : 713031725 ≤ 717226029) (by decide : 717226029 ≤ 721420333) join01 join23

end
end B85
end Sude.FastTwinScan
