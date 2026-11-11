import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B64 (S256..S259). -/
namespace Sude.FastTwinScan
namespace B64
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 536870957 538968109 = 6855 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 536870957 538968109).card = 6855 := by
  have h := fastStrideSixIntervalScan_spec 536870957 538968109 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 538968109 541065261 = 6806 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 538968109 541065261).card = 6806 := by
  have h := fastStrideSixIntervalScan_spec 538968109 541065261 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 541065261 543162413 = 6762 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 541065261 543162413).card = 6762 := by
  have h := fastStrideSixIntervalScan_spec 541065261 543162413 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 543162413 545259565 = 6965 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 543162413 545259565).card = 6965 := by
  have h := fastStrideSixIntervalScan_spec 543162413 545259565 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 536870957 541065261).card = 13661 := by
  simpa using combineTwinPrimeSegments (by decide : 536870957 ≤ 538968109) (by decide : 538968109 ≤ 541065261) seg0 seg1

theorem join23 : (twinPrimeSegment 541065261 545259565).card = 13727 := by
  simpa using combineTwinPrimeSegments (by decide : 541065261 ≤ 543162413) (by decide : 543162413 ≤ 545259565) seg2 seg3

theorem total : (twinPrimeSegment 536870957 545259565).card = 27388 := by
  simpa using combineTwinPrimeSegments (by decide : 536870957 ≤ 541065261) (by decide : 541065261 ≤ 545259565) join01 join23

end
end B64
end Sude.FastTwinScan
