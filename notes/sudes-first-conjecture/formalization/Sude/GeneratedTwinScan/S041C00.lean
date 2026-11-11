import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S041C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85983277 86016045 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 85983277 86016045).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85983277 86016045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86016045 86048813 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 86016045 86048813).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86016045 86048813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86048813 86081581 = 146 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 86048813 86081581).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86048813 86081581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86081581 86114349 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 86081581 86114349).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86081581 86114349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 85983277 86048813).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 85983277 ≤ 86016045)
    (by decide : 86016045 ≤ 86048813) block0 block1

theorem join_0_1 : (twinPrimeSegment 86048813 86114349).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 86048813 ≤ 86081581)
    (by decide : 86081581 ≤ 86114349) block2 block3

theorem join_1_0 : (twinPrimeSegment 85983277 86114349).card = 519 := by
  simpa using combineTwinPrimeSegments (by decide : 85983277 ≤ 86048813)
    (by decide : 86048813 ≤ 86114349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 85983277 86114349).card = 519 := join_1_0

end S041C00
end Sude.GeneratedTwinScan
