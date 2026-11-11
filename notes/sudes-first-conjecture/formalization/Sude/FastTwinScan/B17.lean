import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B17 (S068..S071). -/
namespace Sude.FastTwinScan
namespace B17
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 142606381 144703533 = 7934 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 142606381 144703533).card = 7934 := by
  have h := fastStrideSixIntervalScan_spec 142606381 144703533 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 144703533 146800685 = 7766 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 144703533 146800685).card = 7766 := by
  have h := fastStrideSixIntervalScan_spec 144703533 146800685 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 146800685 148897837 = 7792 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 146800685 148897837).card = 7792 := by
  have h := fastStrideSixIntervalScan_spec 146800685 148897837 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 148897837 150994989 = 7723 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 148897837 150994989).card = 7723 := by
  have h := fastStrideSixIntervalScan_spec 148897837 150994989 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 142606381 146800685).card = 15700 := by
  simpa using combineTwinPrimeSegments (by decide : 142606381 ≤ 144703533) (by decide : 144703533 ≤ 146800685) seg0 seg1

theorem join23 : (twinPrimeSegment 146800685 150994989).card = 15515 := by
  simpa using combineTwinPrimeSegments (by decide : 146800685 ≤ 148897837) (by decide : 148897837 ≤ 150994989) seg2 seg3

theorem total : (twinPrimeSegment 142606381 150994989).card = 31215 := by
  simpa using combineTwinPrimeSegments (by decide : 142606381 ≤ 146800685) (by decide : 146800685 ≤ 150994989) join01 join23

end
end B17
end Sude.FastTwinScan
