import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B54 (S216..S219). -/
namespace Sude.FastTwinScan
namespace B54
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 452984877 455082029 = 7035 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 452984877 455082029).card = 7035 := by
  have h := fastStrideSixIntervalScan_spec 452984877 455082029 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 455082029 457179181 = 7015 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 455082029 457179181).card = 7015 := by
  have h := fastStrideSixIntervalScan_spec 455082029 457179181 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 457179181 459276333 = 6949 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 457179181 459276333).card = 6949 := by
  have h := fastStrideSixIntervalScan_spec 457179181 459276333 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 459276333 461373485 = 6916 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 459276333 461373485).card = 6916 := by
  have h := fastStrideSixIntervalScan_spec 459276333 461373485 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 452984877 457179181).card = 14050 := by
  simpa using combineTwinPrimeSegments (by decide : 452984877 ≤ 455082029) (by decide : 455082029 ≤ 457179181) seg0 seg1

theorem join23 : (twinPrimeSegment 457179181 461373485).card = 13865 := by
  simpa using combineTwinPrimeSegments (by decide : 457179181 ≤ 459276333) (by decide : 459276333 ≤ 461373485) seg2 seg3

theorem total : (twinPrimeSegment 452984877 461373485).card = 27915 := by
  simpa using combineTwinPrimeSegments (by decide : 452984877 ≤ 457179181) (by decide : 457179181 ≤ 461373485) join01 join23

end
end B54
end Sude.FastTwinScan
