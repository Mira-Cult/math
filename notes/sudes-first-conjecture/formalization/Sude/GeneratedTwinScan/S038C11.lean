import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S038C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81133613 81166381 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 81133613 81166381).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81133613 81166381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81166381 81199149 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 81166381 81199149).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81166381 81199149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81199149 81231917 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 81199149 81231917).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81199149 81231917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81231917 81264685 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 81231917 81264685).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81231917 81264685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 81133613 81199149).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 81133613 ≤ 81166381)
    (by decide : 81166381 ≤ 81199149) block0 block1

theorem join_0_1 : (twinPrimeSegment 81199149 81264685).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 81199149 ≤ 81231917)
    (by decide : 81231917 ≤ 81264685) block2 block3

theorem join_1_0 : (twinPrimeSegment 81133613 81264685).card = 534 := by
  simpa using combineTwinPrimeSegments (by decide : 81133613 ≤ 81199149)
    (by decide : 81199149 ≤ 81264685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 81133613 81264685).card = 534 := join_1_0

end S038C11
end Sude.GeneratedTwinScan
