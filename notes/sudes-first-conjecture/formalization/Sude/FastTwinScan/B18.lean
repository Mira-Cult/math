import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B18 (S072..S075). -/
namespace Sude.FastTwinScan
namespace B18
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 150994989 153092141 = 7709 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 150994989 153092141).card = 7709 := by
  have h := fastStrideSixIntervalScan_spec 150994989 153092141 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 153092141 155189293 = 7799 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 153092141 155189293).card = 7799 := by
  have h := fastStrideSixIntervalScan_spec 153092141 155189293 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 155189293 157286445 = 7866 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 155189293 157286445).card = 7866 := by
  have h := fastStrideSixIntervalScan_spec 155189293 157286445 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 157286445 159383597 = 7850 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 157286445 159383597).card = 7850 := by
  have h := fastStrideSixIntervalScan_spec 157286445 159383597 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 150994989 155189293).card = 15508 := by
  simpa using combineTwinPrimeSegments (by decide : 150994989 ≤ 153092141) (by decide : 153092141 ≤ 155189293) seg0 seg1

theorem join23 : (twinPrimeSegment 155189293 159383597).card = 15716 := by
  simpa using combineTwinPrimeSegments (by decide : 155189293 ≤ 157286445) (by decide : 157286445 ≤ 159383597) seg2 seg3

theorem total : (twinPrimeSegment 150994989 159383597).card = 31224 := by
  simpa using combineTwinPrimeSegments (by decide : 150994989 ≤ 155189293) (by decide : 155189293 ≤ 159383597) join01 join23

end
end B18
end Sude.FastTwinScan
