import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S063C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133955629 133988397 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 133955629 133988397).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133955629 133988397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133988397 134021165 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 133988397 134021165).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133988397 134021165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134021165 134053933 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 134021165 134053933).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134021165 134053933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134053933 134086701 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 134053933 134086701).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134053933 134086701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 133955629 134021165).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 133955629 ≤ 133988397)
    (by decide : 133988397 ≤ 134021165) block0 block1

theorem join_0_1 : (twinPrimeSegment 134021165 134086701).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 134021165 ≤ 134053933)
    (by decide : 134053933 ≤ 134086701) block2 block3

theorem join_1_0 : (twinPrimeSegment 133955629 134086701).card = 519 := by
  simpa using combineTwinPrimeSegments (by decide : 133955629 ≤ 134021165)
    (by decide : 134021165 ≤ 134086701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 133955629 134086701).card = 519 := join_1_0

end S063C14
end Sude.GeneratedTwinScan
