import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B06 (S024..S027). -/
namespace Sude.FastTwinScan
namespace B06
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 50331693 52428845 = 8665 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 50331693 52428845).card = 8665 := by
  have h := fastStrideSixIntervalScan_spec 50331693 52428845 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 52428845 54525997 = 8788 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 52428845 54525997).card = 8788 := by
  have h := fastStrideSixIntervalScan_spec 52428845 54525997 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 54525997 56623149 = 8740 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 54525997 56623149).card = 8740 := by
  have h := fastStrideSixIntervalScan_spec 54525997 56623149 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 56623149 58720301 = 8686 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 56623149 58720301).card = 8686 := by
  have h := fastStrideSixIntervalScan_spec 56623149 58720301 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 50331693 54525997).card = 17453 := by
  simpa using combineTwinPrimeSegments (by decide : 50331693 ≤ 52428845) (by decide : 52428845 ≤ 54525997) seg0 seg1

theorem join23 : (twinPrimeSegment 54525997 58720301).card = 17426 := by
  simpa using combineTwinPrimeSegments (by decide : 54525997 ≤ 56623149) (by decide : 56623149 ≤ 58720301) seg2 seg3

theorem total : (twinPrimeSegment 50331693 58720301).card = 34879 := by
  simpa using combineTwinPrimeSegments (by decide : 50331693 ≤ 54525997) (by decide : 54525997 ≤ 58720301) join01 join23

end
end B06
end Sude.FastTwinScan
