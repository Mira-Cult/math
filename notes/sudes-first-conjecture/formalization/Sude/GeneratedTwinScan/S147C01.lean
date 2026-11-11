import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S147C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17562)) 308412461 308445229 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 308412461 308445229).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17562 308412461 308445229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17563)) 308445229 308477997 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 308445229 308477997).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17563 308445229 308477997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17564)) 308477997 308510765 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 308477997 308510765).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17564 308477997 308510765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17565)) 308510765 308543533 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 308510765 308543533).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17565 308510765 308543533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 308412461 308477997).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 308412461 ≤ 308445229)
    (by decide : 308445229 ≤ 308477997) block0 block1

theorem join_0_1 : (twinPrimeSegment 308477997 308543533).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 308477997 ≤ 308510765)
    (by decide : 308510765 ≤ 308543533) block2 block3

theorem join_1_0 : (twinPrimeSegment 308412461 308543533).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 308412461 ≤ 308477997)
    (by decide : 308477997 ≤ 308543533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 308412461 308543533).card = 478 := join_1_0

end S147C01
end Sude.GeneratedTwinScan
