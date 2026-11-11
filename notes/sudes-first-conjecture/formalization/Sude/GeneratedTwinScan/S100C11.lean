import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S100C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14532)) 211157037 211189805 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 211157037 211189805).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14532 211157037 211189805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14533)) 211189805 211222573 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 211189805 211222573).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14533 211189805 211222573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14534)) 211222573 211255341 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 211222573 211255341).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14534 211222573 211255341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14535)) 211255341 211288109 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 211255341 211288109).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14535 211255341 211288109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 211157037 211222573).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 211157037 ≤ 211189805)
    (by decide : 211189805 ≤ 211222573) block0 block1

theorem join_0_1 : (twinPrimeSegment 211222573 211288109).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 211222573 ≤ 211255341)
    (by decide : 211255341 ≤ 211288109) block2 block3

theorem join_1_0 : (twinPrimeSegment 211157037 211288109).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 211157037 ≤ 211222573)
    (by decide : 211222573 ≤ 211288109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 211157037 211288109).card = 471 := join_1_0

end S100C11
end Sude.GeneratedTwinScan
