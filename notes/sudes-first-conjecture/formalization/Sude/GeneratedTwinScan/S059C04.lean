import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S059C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124256301 124289069 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 124256301 124289069).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124256301 124289069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124289069 124321837 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 124289069 124321837).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124289069 124321837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124321837 124354605 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 124321837 124354605).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124321837 124354605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124354605 124387373 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 124354605 124387373).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124354605 124387373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 124256301 124321837).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 124256301 ≤ 124289069)
    (by decide : 124289069 ≤ 124321837) block0 block1

theorem join_0_1 : (twinPrimeSegment 124321837 124387373).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 124321837 ≤ 124354605)
    (by decide : 124354605 ≤ 124387373) block2 block3

theorem join_1_0 : (twinPrimeSegment 124256301 124387373).card = 513 := by
  simpa using combineTwinPrimeSegments (by decide : 124256301 ≤ 124321837)
    (by decide : 124321837 ≤ 124387373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 124256301 124387373).card = 513 := join_1_0

end S059C04
end Sude.GeneratedTwinScan
