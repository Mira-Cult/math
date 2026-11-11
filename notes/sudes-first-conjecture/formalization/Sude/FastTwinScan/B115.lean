import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B115 (S460..S463). -/
namespace Sude.FastTwinScan
namespace B115
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 964689965 966787117 = 6416 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 964689965 966787117).card = 6416 := by
  have h := fastStrideSixIntervalScan_spec 964689965 966787117 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 966787117 968884269 = 6583 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 966787117 968884269).card = 6583 := by
  have h := fastStrideSixIntervalScan_spec 966787117 968884269 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 968884269 970981421 = 6540 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 968884269 970981421).card = 6540 := by
  have h := fastStrideSixIntervalScan_spec 968884269 970981421 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 970981421 973078573 = 6410 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 970981421 973078573).card = 6410 := by
  have h := fastStrideSixIntervalScan_spec 970981421 973078573 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 964689965 968884269).card = 12999 := by
  simpa using combineTwinPrimeSegments (by decide : 964689965 ≤ 966787117) (by decide : 966787117 ≤ 968884269) seg0 seg1

theorem join23 : (twinPrimeSegment 968884269 973078573).card = 12950 := by
  simpa using combineTwinPrimeSegments (by decide : 968884269 ≤ 970981421) (by decide : 970981421 ≤ 973078573) seg2 seg3

theorem total : (twinPrimeSegment 964689965 973078573).card = 25949 := by
  simpa using combineTwinPrimeSegments (by decide : 964689965 ≤ 968884269) (by decide : 968884269 ≤ 973078573) join01 join23

end
end B115
end Sude.FastTwinScan
