import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B32 (S128..S131). -/
namespace Sude.FastTwinScan
namespace B32
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 268435501 270532653 = 7357 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 268435501 270532653).card = 7357 := by
  have h := fastStrideSixIntervalScan_spec 268435501 270532653 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 270532653 272629805 = 7352 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 270532653 272629805).card = 7352 := by
  have h := fastStrideSixIntervalScan_spec 270532653 272629805 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 272629805 274726957 = 7272 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 272629805 274726957).card = 7272 := by
  have h := fastStrideSixIntervalScan_spec 272629805 274726957 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 274726957 276824109 = 7299 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 274726957 276824109).card = 7299 := by
  have h := fastStrideSixIntervalScan_spec 274726957 276824109 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 268435501 272629805).card = 14709 := by
  simpa using combineTwinPrimeSegments (by decide : 268435501 ≤ 270532653) (by decide : 270532653 ≤ 272629805) seg0 seg1

theorem join23 : (twinPrimeSegment 272629805 276824109).card = 14571 := by
  simpa using combineTwinPrimeSegments (by decide : 272629805 ≤ 274726957) (by decide : 274726957 ≤ 276824109) seg2 seg3

theorem total : (twinPrimeSegment 268435501 276824109).card = 29280 := by
  simpa using combineTwinPrimeSegments (by decide : 268435501 ≤ 272629805) (by decide : 272629805 ≤ 276824109) join01 join23

end
end B32
end Sude.FastTwinScan
