import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S068C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142606381 142639149 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 142606381 142639149).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142606381 142639149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142639149 142671917 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 142639149 142671917).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142639149 142671917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142671917 142704685 = 146 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 142671917 142704685).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142671917 142704685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142704685 142737453 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 142704685 142737453).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142704685 142737453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 142606381 142671917).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 142606381 ≤ 142639149)
    (by decide : 142639149 ≤ 142671917) block0 block1

theorem join_0_1 : (twinPrimeSegment 142671917 142737453).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 142671917 ≤ 142704685)
    (by decide : 142704685 ≤ 142737453) block2 block3

theorem join_1_0 : (twinPrimeSegment 142606381 142737453).card = 498 := by
  simpa using combineTwinPrimeSegments (by decide : 142606381 ≤ 142671917)
    (by decide : 142671917 ≤ 142737453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 142606381 142737453).card = 498 := join_1_0

end S068C00
end Sude.GeneratedTwinScan
