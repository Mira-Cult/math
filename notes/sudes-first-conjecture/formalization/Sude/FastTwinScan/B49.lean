import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B49 (S196..S199). -/
namespace Sude.FastTwinScan
namespace B49
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 411041837 413138989 = 7023 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 411041837 413138989).card = 7023 := by
  have h := fastStrideSixIntervalScan_spec 411041837 413138989 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 413138989 415236141 = 6983 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 413138989 415236141).card = 6983 := by
  have h := fastStrideSixIntervalScan_spec 413138989 415236141 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 415236141 417333293 = 7051 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 415236141 417333293).card = 7051 := by
  have h := fastStrideSixIntervalScan_spec 415236141 417333293 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 417333293 419430445 = 7120 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 417333293 419430445).card = 7120 := by
  have h := fastStrideSixIntervalScan_spec 417333293 419430445 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 411041837 415236141).card = 14006 := by
  simpa using combineTwinPrimeSegments (by decide : 411041837 ≤ 413138989) (by decide : 413138989 ≤ 415236141) seg0 seg1

theorem join23 : (twinPrimeSegment 415236141 419430445).card = 14171 := by
  simpa using combineTwinPrimeSegments (by decide : 415236141 ≤ 417333293) (by decide : 417333293 ≤ 419430445) seg2 seg3

theorem total : (twinPrimeSegment 411041837 419430445).card = 28177 := by
  simpa using combineTwinPrimeSegments (by decide : 411041837 ≤ 415236141) (by decide : 415236141 ≤ 419430445) join01 join23

end
end B49
end Sude.FastTwinScan
