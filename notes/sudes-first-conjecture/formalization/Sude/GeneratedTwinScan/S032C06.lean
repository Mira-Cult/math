import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S032C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67895341 67928109 = 147 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 67895341 67928109).card = 147 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67895341 67928109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67928109 67960877 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 67928109 67960877).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67928109 67960877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67960877 67993645 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 67960877 67993645).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67960877 67993645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67993645 68026413 = 159 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 67993645 68026413).card = 159 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67993645 68026413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 67895341 67960877).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 67895341 ≤ 67928109)
    (by decide : 67928109 ≤ 67960877) block0 block1

theorem join_0_1 : (twinPrimeSegment 67960877 68026413).card = 294 := by
  simpa using combineTwinPrimeSegments (by decide : 67960877 ≤ 67993645)
    (by decide : 67993645 ≤ 68026413) block2 block3

theorem join_1_0 : (twinPrimeSegment 67895341 68026413).card = 555 := by
  simpa using combineTwinPrimeSegments (by decide : 67895341 ≤ 67960877)
    (by decide : 67960877 ≤ 68026413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 67895341 68026413).card = 555 := join_1_0

end S032C06
end Sude.GeneratedTwinScan
