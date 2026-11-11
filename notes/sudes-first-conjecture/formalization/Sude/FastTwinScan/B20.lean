import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B20 (S080..S083). -/
namespace Sude.FastTwinScan
namespace B20
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 167772205 169869357 = 7689 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 167772205 169869357).card = 7689 := by
  have h := fastStrideSixIntervalScan_spec 167772205 169869357 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 169869357 171966509 = 7659 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 169869357 171966509).card = 7659 := by
  have h := fastStrideSixIntervalScan_spec 169869357 171966509 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 171966509 174063661 = 7622 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 171966509 174063661).card = 7622 := by
  have h := fastStrideSixIntervalScan_spec 171966509 174063661 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 174063661 176160813 = 7740 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 174063661 176160813).card = 7740 := by
  have h := fastStrideSixIntervalScan_spec 174063661 176160813 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 167772205 171966509).card = 15348 := by
  simpa using combineTwinPrimeSegments (by decide : 167772205 ≤ 169869357) (by decide : 169869357 ≤ 171966509) seg0 seg1

theorem join23 : (twinPrimeSegment 171966509 176160813).card = 15362 := by
  simpa using combineTwinPrimeSegments (by decide : 171966509 ≤ 174063661) (by decide : 174063661 ≤ 176160813) seg2 seg3

theorem total : (twinPrimeSegment 167772205 176160813).card = 30710 := by
  simpa using combineTwinPrimeSegments (by decide : 167772205 ≤ 171966509) (by decide : 171966509 ≤ 176160813) join01 join23

end
end B20
end Sude.FastTwinScan
