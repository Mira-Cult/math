import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S034C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73007149 73039917 = 141 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 73007149 73039917).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73007149 73039917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73039917 73072685 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 73039917 73072685).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73039917 73072685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73072685 73105453 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 73072685 73105453).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73072685 73105453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73105453 73138221 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 73105453 73138221).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73105453 73138221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 73007149 73072685).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 73007149 ≤ 73039917)
    (by decide : 73039917 ≤ 73072685) block0 block1

theorem join_0_1 : (twinPrimeSegment 73072685 73138221).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 73072685 ≤ 73105453)
    (by decide : 73105453 ≤ 73138221) block2 block3

theorem join_1_0 : (twinPrimeSegment 73007149 73138221).card = 524 := by
  simpa using combineTwinPrimeSegments (by decide : 73007149 ≤ 73072685)
    (by decide : 73072685 ≤ 73138221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 73007149 73138221).card = 524 := join_1_0

end S034C13
end Sude.GeneratedTwinScan
