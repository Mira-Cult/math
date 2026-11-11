import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B121 (S484..S487). -/
namespace Sude.FastTwinScan
namespace B121
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 1015021613 1017118765 = 6424 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 1015021613 1017118765).card = 6424 := by
  have h := fastStrideSixIntervalScan_spec 1015021613 1017118765 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 1017118765 1019215917 = 6437 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 1017118765 1019215917).card = 6437 := by
  have h := fastStrideSixIntervalScan_spec 1017118765 1019215917 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 1019215917 1021313069 = 6521 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 1019215917 1021313069).card = 6521 := by
  have h := fastStrideSixIntervalScan_spec 1019215917 1021313069 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 1021313069 1023410221 = 6409 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 1021313069 1023410221).card = 6409 := by
  have h := fastStrideSixIntervalScan_spec 1021313069 1023410221 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 1015021613 1019215917).card = 12861 := by
  simpa using combineTwinPrimeSegments (by decide : 1015021613 ≤ 1017118765) (by decide : 1017118765 ≤ 1019215917) seg0 seg1

theorem join23 : (twinPrimeSegment 1019215917 1023410221).card = 12930 := by
  simpa using combineTwinPrimeSegments (by decide : 1019215917 ≤ 1021313069) (by decide : 1021313069 ≤ 1023410221) seg2 seg3

theorem total : (twinPrimeSegment 1015021613 1023410221).card = 25791 := by
  simpa using combineTwinPrimeSegments (by decide : 1015021613 ≤ 1019215917) (by decide : 1019215917 ≤ 1023410221) join01 join23

end
end B121
end Sude.FastTwinScan
