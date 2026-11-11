import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B113 (S452..S455). -/
namespace Sude.FastTwinScan
namespace B113
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 947912749 950009901 = 6387 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 947912749 950009901).card = 6387 := by
  have h := fastStrideSixIntervalScan_spec 947912749 950009901 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 950009901 952107053 = 6475 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 950009901 952107053).card = 6475 := by
  have h := fastStrideSixIntervalScan_spec 950009901 952107053 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 952107053 954204205 = 6585 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 952107053 954204205).card = 6585 := by
  have h := fastStrideSixIntervalScan_spec 952107053 954204205 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 954204205 956301357 = 6429 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 954204205 956301357).card = 6429 := by
  have h := fastStrideSixIntervalScan_spec 954204205 956301357 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 947912749 952107053).card = 12862 := by
  simpa using combineTwinPrimeSegments (by decide : 947912749 ≤ 950009901) (by decide : 950009901 ≤ 952107053) seg0 seg1

theorem join23 : (twinPrimeSegment 952107053 956301357).card = 13014 := by
  simpa using combineTwinPrimeSegments (by decide : 952107053 ≤ 954204205) (by decide : 954204205 ≤ 956301357) seg2 seg3

theorem total : (twinPrimeSegment 947912749 956301357).card = 25876 := by
  simpa using combineTwinPrimeSegments (by decide : 947912749 ≤ 952107053) (by decide : 952107053 ≤ 956301357) join01 join23

end
end B113
end Sude.FastTwinScan
