import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S033C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71041069 71073837 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 71041069 71073837).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71041069 71073837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71073837 71106605 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 71073837 71106605).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71073837 71106605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71106605 71139373 = 142 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 71106605 71139373).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71106605 71139373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71139373 71172141 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 71139373 71172141).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71139373 71172141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 71041069 71106605).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 71041069 ≤ 71073837)
    (by decide : 71073837 ≤ 71106605) block0 block1

theorem join_0_1 : (twinPrimeSegment 71106605 71172141).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 71106605 ≤ 71139373)
    (by decide : 71139373 ≤ 71172141) block2 block3

theorem join_1_0 : (twinPrimeSegment 71041069 71172141).card = 533 := by
  simpa using combineTwinPrimeSegments (by decide : 71041069 ≤ 71106605)
    (by decide : 71106605 ≤ 71172141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 71041069 71172141).card = 533 := join_1_0

end S033C14
end Sude.GeneratedTwinScan
