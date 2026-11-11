import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S032C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68812845 68845613 = 148 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 68812845 68845613).card = 148 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68812845 68845613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68845613 68878381 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 68845613 68878381).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68845613 68878381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68878381 68911149 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 68878381 68911149).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68878381 68911149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68911149 68943917 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 68911149 68943917).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68911149 68943917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 68812845 68878381).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 68812845 ≤ 68845613)
    (by decide : 68845613 ≤ 68878381) block0 block1

theorem join_0_1 : (twinPrimeSegment 68878381 68943917).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 68878381 ≤ 68911149)
    (by decide : 68911149 ≤ 68943917) block2 block3

theorem join_1_0 : (twinPrimeSegment 68812845 68943917).card = 521 := by
  simpa using combineTwinPrimeSegments (by decide : 68812845 ≤ 68878381)
    (by decide : 68878381 ≤ 68943917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 68812845 68943917).card = 521 := join_1_0

end S032C13
end Sude.GeneratedTwinScan
