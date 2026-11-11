import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S041C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86507565 86540333 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 86507565 86540333).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86507565 86540333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86540333 86573101 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 86540333 86573101).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86540333 86573101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86573101 86605869 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 86573101 86605869).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86573101 86605869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86605869 86638637 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 86605869 86638637).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86605869 86638637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 86507565 86573101).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 86507565 ≤ 86540333)
    (by decide : 86540333 ≤ 86573101) block0 block1

theorem join_0_1 : (twinPrimeSegment 86573101 86638637).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 86573101 ≤ 86605869)
    (by decide : 86605869 ≤ 86638637) block2 block3

theorem join_1_0 : (twinPrimeSegment 86507565 86638637).card = 529 := by
  simpa using combineTwinPrimeSegments (by decide : 86507565 ≤ 86573101)
    (by decide : 86573101 ≤ 86638637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 86507565 86638637).card = 529 := join_1_0

end S041C04
end Sude.GeneratedTwinScan
