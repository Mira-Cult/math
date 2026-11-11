import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B87 (S348..S351). -/
namespace Sude.FastTwinScan
namespace B87
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 729808941 731906093 = 6535 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 729808941 731906093).card = 6535 := by
  have h := fastStrideSixIntervalScan_spec 729808941 731906093 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 731906093 734003245 = 6654 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 731906093 734003245).card = 6654 := by
  have h := fastStrideSixIntervalScan_spec 731906093 734003245 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 734003245 736100397 = 6678 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 734003245 736100397).card = 6678 := by
  have h := fastStrideSixIntervalScan_spec 734003245 736100397 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 736100397 738197549 = 6666 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 736100397 738197549).card = 6666 := by
  have h := fastStrideSixIntervalScan_spec 736100397 738197549 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 729808941 734003245).card = 13189 := by
  simpa using combineTwinPrimeSegments (by decide : 729808941 ≤ 731906093) (by decide : 731906093 ≤ 734003245) seg0 seg1

theorem join23 : (twinPrimeSegment 734003245 738197549).card = 13344 := by
  simpa using combineTwinPrimeSegments (by decide : 734003245 ≤ 736100397) (by decide : 736100397 ≤ 738197549) seg2 seg3

theorem total : (twinPrimeSegment 729808941 738197549).card = 26533 := by
  simpa using combineTwinPrimeSegments (by decide : 729808941 ≤ 734003245) (by decide : 734003245 ≤ 738197549) join01 join23

end
end B87
end Sude.FastTwinScan
