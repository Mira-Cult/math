import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B92 (S368..S371). -/
namespace Sude.FastTwinScan
namespace B92
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 771751981 773849133 = 6591 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 771751981 773849133).card = 6591 := by
  have h := fastStrideSixIntervalScan_spec 771751981 773849133 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 773849133 775946285 = 6661 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 773849133 775946285).card = 6661 := by
  have h := fastStrideSixIntervalScan_spec 773849133 775946285 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 775946285 778043437 = 6617 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 775946285 778043437).card = 6617 := by
  have h := fastStrideSixIntervalScan_spec 775946285 778043437 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 778043437 780140589 = 6625 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 778043437 780140589).card = 6625 := by
  have h := fastStrideSixIntervalScan_spec 778043437 780140589 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 771751981 775946285).card = 13252 := by
  simpa using combineTwinPrimeSegments (by decide : 771751981 ≤ 773849133) (by decide : 773849133 ≤ 775946285) seg0 seg1

theorem join23 : (twinPrimeSegment 775946285 780140589).card = 13242 := by
  simpa using combineTwinPrimeSegments (by decide : 775946285 ≤ 778043437) (by decide : 778043437 ≤ 780140589) seg2 seg3

theorem total : (twinPrimeSegment 771751981 780140589).card = 26494 := by
  simpa using combineTwinPrimeSegments (by decide : 771751981 ≤ 775946285) (by decide : 775946285 ≤ 780140589) join01 join23

end
end B92
end Sude.FastTwinScan
