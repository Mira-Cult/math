import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B02 (S008..S011). -/
namespace Sude.FastTwinScan
namespace B02
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 16777261 18874413 = 9974 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 16777261 18874413).card = 9974 := by
  have h := fastStrideSixIntervalScan_spec 16777261 18874413 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 18874413 20971565 = 9746 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 18874413 20971565).card = 9746 := by
  have h := fastStrideSixIntervalScan_spec 18874413 20971565 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 20971565 23068717 = 9661 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 20971565 23068717).card = 9661 := by
  have h := fastStrideSixIntervalScan_spec 20971565 23068717 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 23068717 25165869 = 9626 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 23068717 25165869).card = 9626 := by
  have h := fastStrideSixIntervalScan_spec 23068717 25165869 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 16777261 20971565).card = 19720 := by
  simpa using combineTwinPrimeSegments (by decide : 16777261 ≤ 18874413) (by decide : 18874413 ≤ 20971565) seg0 seg1

theorem join23 : (twinPrimeSegment 20971565 25165869).card = 19287 := by
  simpa using combineTwinPrimeSegments (by decide : 20971565 ≤ 23068717) (by decide : 23068717 ≤ 25165869) seg2 seg3

theorem total : (twinPrimeSegment 16777261 25165869).card = 39007 := by
  simpa using combineTwinPrimeSegments (by decide : 16777261 ≤ 20971565) (by decide : 20971565 ≤ 25165869) join01 join23

end
end B02
end Sude.FastTwinScan
