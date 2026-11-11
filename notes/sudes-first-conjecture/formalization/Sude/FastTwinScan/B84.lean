import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B84 (S336..S339). -/
namespace Sude.FastTwinScan
namespace B84
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 704643117 706740269 = 6630 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 704643117 706740269).card = 6630 := by
  have h := fastStrideSixIntervalScan_spec 704643117 706740269 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 706740269 708837421 = 6831 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 706740269 708837421).card = 6831 := by
  have h := fastStrideSixIntervalScan_spec 706740269 708837421 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 708837421 710934573 = 6670 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 708837421 710934573).card = 6670 := by
  have h := fastStrideSixIntervalScan_spec 708837421 710934573 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 710934573 713031725 = 6802 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 710934573 713031725).card = 6802 := by
  have h := fastStrideSixIntervalScan_spec 710934573 713031725 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 704643117 708837421).card = 13461 := by
  simpa using combineTwinPrimeSegments (by decide : 704643117 ≤ 706740269) (by decide : 706740269 ≤ 708837421) seg0 seg1

theorem join23 : (twinPrimeSegment 708837421 713031725).card = 13472 := by
  simpa using combineTwinPrimeSegments (by decide : 708837421 ≤ 710934573) (by decide : 710934573 ≤ 713031725) seg2 seg3

theorem total : (twinPrimeSegment 704643117 713031725).card = 26933 := by
  simpa using combineTwinPrimeSegments (by decide : 704643117 ≤ 708837421) (by decide : 708837421 ≤ 713031725) join01 join23

end
end B84
end Sude.FastTwinScan
