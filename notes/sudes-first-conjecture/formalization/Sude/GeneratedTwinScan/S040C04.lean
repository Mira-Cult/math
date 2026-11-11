import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S040C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84410413 84443181 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 84410413 84443181).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84410413 84443181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84443181 84475949 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 84443181 84475949).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84443181 84475949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84475949 84508717 = 149 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 84475949 84508717).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84475949 84508717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84508717 84541485 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 84508717 84541485).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84508717 84541485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 84410413 84475949).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 84410413 ≤ 84443181)
    (by decide : 84443181 ≤ 84475949) block0 block1

theorem join_0_1 : (twinPrimeSegment 84475949 84541485).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 84475949 ≤ 84508717)
    (by decide : 84508717 ≤ 84541485) block2 block3

theorem join_1_0 : (twinPrimeSegment 84410413 84541485).card = 560 := by
  simpa using combineTwinPrimeSegments (by decide : 84410413 ≤ 84475949)
    (by decide : 84475949 ≤ 84541485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 84410413 84541485).card = 560 := join_1_0

end S040C04
end Sude.GeneratedTwinScan
