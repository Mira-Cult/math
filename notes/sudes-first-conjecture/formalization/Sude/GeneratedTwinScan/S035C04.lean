import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S035C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73924653 73957421 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 73924653 73957421).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73924653 73957421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73957421 73990189 = 159 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 73957421 73990189).card = 159 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73957421 73990189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73990189 74022957 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 73990189 74022957).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73990189 74022957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74022957 74055725 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 74022957 74055725).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74022957 74055725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 73924653 73990189).card = 294 := by
  simpa using combineTwinPrimeSegments (by decide : 73924653 ≤ 73957421)
    (by decide : 73957421 ≤ 73990189) block0 block1

theorem join_0_1 : (twinPrimeSegment 73990189 74055725).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 73990189 ≤ 74022957)
    (by decide : 74022957 ≤ 74055725) block2 block3

theorem join_1_0 : (twinPrimeSegment 73924653 74055725).card = 554 := by
  simpa using combineTwinPrimeSegments (by decide : 73924653 ≤ 73990189)
    (by decide : 73990189 ≤ 74055725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 73924653 74055725).card = 554 := join_1_0

end S035C04
end Sude.GeneratedTwinScan
