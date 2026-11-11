import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S063C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133562413 133595181 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 133562413 133595181).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133562413 133595181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133595181 133627949 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 133595181 133627949).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133595181 133627949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133627949 133660717 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 133627949 133660717).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133627949 133660717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133660717 133693485 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 133660717 133693485).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133660717 133693485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 133562413 133627949).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 133562413 ≤ 133595181)
    (by decide : 133595181 ≤ 133627949) block0 block1

theorem join_0_1 : (twinPrimeSegment 133627949 133693485).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 133627949 ≤ 133660717)
    (by decide : 133660717 ≤ 133693485) block2 block3

theorem join_1_0 : (twinPrimeSegment 133562413 133693485).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 133562413 ≤ 133627949)
    (by decide : 133627949 ≤ 133693485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 133562413 133693485).card = 494 := join_1_0

end S063C11
end Sude.GeneratedTwinScan
