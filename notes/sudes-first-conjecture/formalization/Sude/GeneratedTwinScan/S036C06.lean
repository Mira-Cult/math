import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S036C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76283949 76316717 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 76283949 76316717).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76283949 76316717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76316717 76349485 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 76316717 76349485).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76316717 76349485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76349485 76382253 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 76349485 76382253).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76349485 76382253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76382253 76415021 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 76382253 76415021).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76382253 76415021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 76283949 76349485).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 76283949 ≤ 76316717)
    (by decide : 76316717 ≤ 76349485) block0 block1

theorem join_0_1 : (twinPrimeSegment 76349485 76415021).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 76349485 ≤ 76382253)
    (by decide : 76382253 ≤ 76415021) block2 block3

theorem join_1_0 : (twinPrimeSegment 76283949 76415021).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 76283949 ≤ 76349485)
    (by decide : 76349485 ≤ 76415021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 76283949 76415021).card = 494 := join_1_0

end S036C06
end Sude.GeneratedTwinScan
