import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S032C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68943917 68976685 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 68943917 68976685).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68943917 68976685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68976685 69009453 = 145 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 68976685 69009453).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68976685 69009453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69009453 69042221 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 69009453 69042221).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69009453 69042221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69042221 69074989 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 69042221 69074989).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69042221 69074989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 68943917 69009453).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 68943917 ≤ 68976685)
    (by decide : 68976685 ≤ 69009453) block0 block1

theorem join_0_1 : (twinPrimeSegment 69009453 69074989).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 69009453 ≤ 69042221)
    (by decide : 69042221 ≤ 69074989) block2 block3

theorem join_1_0 : (twinPrimeSegment 68943917 69074989).card = 517 := by
  simpa using combineTwinPrimeSegments (by decide : 68943917 ≤ 69009453)
    (by decide : 69009453 ≤ 69074989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 68943917 69074989).card = 517 := join_1_0

end S032C14
end Sude.GeneratedTwinScan
