import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S049C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102891565 102924333 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 102891565 102924333).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102891565 102924333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102924333 102957101 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 102924333 102957101).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102924333 102957101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102957101 102989869 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 102957101 102989869).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102957101 102989869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102989869 103022637 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 102989869 103022637).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102989869 103022637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 102891565 102957101).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 102891565 ≤ 102924333)
    (by decide : 102924333 ≤ 102957101) block0 block1

theorem join_0_1 : (twinPrimeSegment 102957101 103022637).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 102957101 ≤ 102989869)
    (by decide : 102989869 ≤ 103022637) block2 block3

theorem join_1_0 : (twinPrimeSegment 102891565 103022637).card = 530 := by
  simpa using combineTwinPrimeSegments (by decide : 102891565 ≤ 102957101)
    (by decide : 102957101 ≤ 103022637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 102891565 103022637).card = 530 := join_1_0

end S049C01
end Sude.GeneratedTwinScan
