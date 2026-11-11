import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S045C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95289389 95322157 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 95289389 95322157).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95289389 95322157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95322157 95354925 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 95322157 95354925).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95322157 95354925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95354925 95387693 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 95354925 95387693).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95354925 95387693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95387693 95420461 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 95387693 95420461).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95387693 95420461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 95289389 95354925).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 95289389 ≤ 95322157)
    (by decide : 95322157 ≤ 95354925) block0 block1

theorem join_0_1 : (twinPrimeSegment 95354925 95420461).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 95354925 ≤ 95387693)
    (by decide : 95387693 ≤ 95420461) block2 block3

theorem join_1_0 : (twinPrimeSegment 95289389 95420461).card = 516 := by
  simpa using combineTwinPrimeSegments (by decide : 95289389 ≤ 95354925)
    (by decide : 95354925 ≤ 95420461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 95289389 95420461).card = 516 := join_1_0

end S045C07
end Sude.GeneratedTwinScan
