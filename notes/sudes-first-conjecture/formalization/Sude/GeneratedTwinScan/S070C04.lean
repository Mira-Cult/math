import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S070C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147324973 147357741 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 147324973 147357741).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147324973 147357741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147357741 147390509 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 147357741 147390509).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147357741 147390509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147390509 147423277 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 147390509 147423277).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147390509 147423277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147423277 147456045 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 147423277 147456045).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147423277 147456045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 147324973 147390509).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 147324973 ≤ 147357741)
    (by decide : 147357741 ≤ 147390509) block0 block1

theorem join_0_1 : (twinPrimeSegment 147390509 147456045).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 147390509 ≤ 147423277)
    (by decide : 147423277 ≤ 147456045) block2 block3

theorem join_1_0 : (twinPrimeSegment 147324973 147456045).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 147324973 ≤ 147390509)
    (by decide : 147390509 ≤ 147456045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 147324973 147456045).card = 486 := join_1_0

end S070C04
end Sude.GeneratedTwinScan
