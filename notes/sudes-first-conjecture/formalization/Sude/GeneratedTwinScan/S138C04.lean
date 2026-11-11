import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S138C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17028)) 289931309 289964077 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 289931309 289964077).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17028 289931309 289964077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17029)) 289964077 289996845 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 289964077 289996845).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17029 289964077 289996845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17030)) 289996845 290029613 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 289996845 290029613).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17030 289996845 290029613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17031)) 290029613 290062381 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 290029613 290062381).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17031 290029613 290062381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 289931309 289996845).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 289931309 ≤ 289964077)
    (by decide : 289964077 ≤ 289996845) block0 block1

theorem join_0_1 : (twinPrimeSegment 289996845 290062381).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 289996845 ≤ 290029613)
    (by decide : 290029613 ≤ 290062381) block2 block3

theorem join_1_0 : (twinPrimeSegment 289931309 290062381).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 289931309 ≤ 289996845)
    (by decide : 289996845 ≤ 290062381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 289931309 290062381).card = 438 := join_1_0

end S138C04
end Sude.GeneratedTwinScan
