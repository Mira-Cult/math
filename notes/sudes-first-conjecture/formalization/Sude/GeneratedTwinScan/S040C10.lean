import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S040C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85196845 85229613 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 85196845 85229613).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85196845 85229613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85229613 85262381 = 142 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 85229613 85262381).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85229613 85262381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85262381 85295149 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 85262381 85295149).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85262381 85295149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85295149 85327917 = 155 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 85295149 85327917).card = 155 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85295149 85327917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 85196845 85262381).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 85196845 ≤ 85229613)
    (by decide : 85229613 ≤ 85262381) block0 block1

theorem join_0_1 : (twinPrimeSegment 85262381 85327917).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 85262381 ≤ 85295149)
    (by decide : 85295149 ≤ 85327917) block2 block3

theorem join_1_0 : (twinPrimeSegment 85196845 85327917).card = 536 := by
  simpa using combineTwinPrimeSegments (by decide : 85196845 ≤ 85262381)
    (by decide : 85262381 ≤ 85327917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 85196845 85327917).card = 536 := join_1_0

end S040C10
end Sude.GeneratedTwinScan
