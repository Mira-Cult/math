import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S053C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111804461 111837229 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 111804461 111837229).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111804461 111837229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111837229 111869997 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 111837229 111869997).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111837229 111869997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111869997 111902765 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 111869997 111902765).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111869997 111902765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111902765 111935533 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 111902765 111935533).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111902765 111935533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 111804461 111869997).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 111804461 ≤ 111837229)
    (by decide : 111837229 ≤ 111869997) block0 block1

theorem join_0_1 : (twinPrimeSegment 111869997 111935533).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 111869997 ≤ 111902765)
    (by decide : 111902765 ≤ 111935533) block2 block3

theorem join_1_0 : (twinPrimeSegment 111804461 111935533).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 111804461 ≤ 111869997)
    (by decide : 111869997 ≤ 111935533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 111804461 111935533).card = 488 := join_1_0

end S053C05
end Sude.GeneratedTwinScan
