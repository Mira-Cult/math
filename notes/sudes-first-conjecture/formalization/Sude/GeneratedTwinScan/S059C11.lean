import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S059C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125173805 125206573 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 125173805 125206573).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125173805 125206573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125206573 125239341 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 125206573 125239341).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125206573 125239341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125239341 125272109 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 125239341 125272109).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125239341 125272109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125272109 125304877 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 125272109 125304877).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125272109 125304877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 125173805 125239341).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 125173805 ≤ 125206573)
    (by decide : 125206573 ≤ 125239341) block0 block1

theorem join_0_1 : (twinPrimeSegment 125239341 125304877).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 125239341 ≤ 125272109)
    (by decide : 125272109 ≤ 125304877) block2 block3

theorem join_1_0 : (twinPrimeSegment 125173805 125304877).card = 505 := by
  simpa using combineTwinPrimeSegments (by decide : 125173805 ≤ 125239341)
    (by decide : 125239341 ≤ 125304877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 125173805 125304877).card = 505 := join_1_0

end S059C11
end Sude.GeneratedTwinScan
