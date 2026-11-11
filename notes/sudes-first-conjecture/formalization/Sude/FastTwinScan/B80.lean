import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B80 (S320..S323). -/
namespace Sude.FastTwinScan
namespace B80
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 671088685 673185837 = 6643 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 671088685 673185837).card = 6643 := by
  have h := fastStrideSixIntervalScan_spec 671088685 673185837 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 673185837 675282989 = 6719 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 673185837 675282989).card = 6719 := by
  have h := fastStrideSixIntervalScan_spec 673185837 675282989 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 675282989 677380141 = 6579 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 675282989 677380141).card = 6579 := by
  have h := fastStrideSixIntervalScan_spec 675282989 677380141 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 677380141 679477293 = 6762 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 677380141 679477293).card = 6762 := by
  have h := fastStrideSixIntervalScan_spec 677380141 679477293 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 671088685 675282989).card = 13362 := by
  simpa using combineTwinPrimeSegments (by decide : 671088685 ≤ 673185837) (by decide : 673185837 ≤ 675282989) seg0 seg1

theorem join23 : (twinPrimeSegment 675282989 679477293).card = 13341 := by
  simpa using combineTwinPrimeSegments (by decide : 675282989 ≤ 677380141) (by decide : 677380141 ≤ 679477293) seg2 seg3

theorem total : (twinPrimeSegment 671088685 679477293).card = 26703 := by
  simpa using combineTwinPrimeSegments (by decide : 671088685 ≤ 675282989) (by decide : 675282989 ≤ 679477293) join01 join23

end
end B80
end Sude.FastTwinScan
