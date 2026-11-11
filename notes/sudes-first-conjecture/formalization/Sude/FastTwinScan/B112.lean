import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B112 (S448..S451). -/
namespace Sude.FastTwinScan
namespace B112
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 939524141 941621293 = 6578 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 939524141 941621293).card = 6578 := by
  have h := fastStrideSixIntervalScan_spec 939524141 941621293 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 941621293 943718445 = 6428 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 941621293 943718445).card = 6428 := by
  have h := fastStrideSixIntervalScan_spec 941621293 943718445 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 943718445 945815597 = 6645 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 943718445 945815597).card = 6645 := by
  have h := fastStrideSixIntervalScan_spec 943718445 945815597 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 945815597 947912749 = 6475 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 945815597 947912749).card = 6475 := by
  have h := fastStrideSixIntervalScan_spec 945815597 947912749 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 939524141 943718445).card = 13006 := by
  simpa using combineTwinPrimeSegments (by decide : 939524141 ≤ 941621293) (by decide : 941621293 ≤ 943718445) seg0 seg1

theorem join23 : (twinPrimeSegment 943718445 947912749).card = 13120 := by
  simpa using combineTwinPrimeSegments (by decide : 943718445 ≤ 945815597) (by decide : 945815597 ≤ 947912749) seg2 seg3

theorem total : (twinPrimeSegment 939524141 947912749).card = 26126 := by
  simpa using combineTwinPrimeSegments (by decide : 939524141 ≤ 943718445) (by decide : 943718445 ≤ 947912749) join01 join23

end
end B112
end Sude.FastTwinScan
