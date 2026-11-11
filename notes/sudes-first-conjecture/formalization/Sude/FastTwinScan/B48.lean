import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B48 (S192..S195). -/
namespace Sude.FastTwinScan
namespace B48
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 402653229 404750381 = 7075 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 402653229 404750381).card = 7075 := by
  have h := fastStrideSixIntervalScan_spec 402653229 404750381 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 404750381 406847533 = 6996 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 404750381 406847533).card = 6996 := by
  have h := fastStrideSixIntervalScan_spec 404750381 406847533 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 406847533 408944685 = 7038 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 406847533 408944685).card = 7038 := by
  have h := fastStrideSixIntervalScan_spec 406847533 408944685 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 408944685 411041837 = 7016 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 408944685 411041837).card = 7016 := by
  have h := fastStrideSixIntervalScan_spec 408944685 411041837 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 402653229 406847533).card = 14071 := by
  simpa using combineTwinPrimeSegments (by decide : 402653229 ≤ 404750381) (by decide : 404750381 ≤ 406847533) seg0 seg1

theorem join23 : (twinPrimeSegment 406847533 411041837).card = 14054 := by
  simpa using combineTwinPrimeSegments (by decide : 406847533 ≤ 408944685) (by decide : 408944685 ≤ 411041837) seg2 seg3

theorem total : (twinPrimeSegment 402653229 411041837).card = 28125 := by
  simpa using combineTwinPrimeSegments (by decide : 402653229 ≤ 406847533) (by decide : 406847533 ≤ 411041837) join01 join23

end
end B48
end Sude.FastTwinScan
