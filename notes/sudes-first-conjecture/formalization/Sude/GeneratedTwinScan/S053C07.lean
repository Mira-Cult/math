import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S053C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112066605 112099373 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 112066605 112099373).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112066605 112099373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112099373 112132141 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 112099373 112132141).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112099373 112132141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112132141 112164909 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 112132141 112164909).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112132141 112164909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112164909 112197677 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 112164909 112197677).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112164909 112197677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 112066605 112132141).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 112066605 ≤ 112099373)
    (by decide : 112099373 ≤ 112132141) block0 block1

theorem join_0_1 : (twinPrimeSegment 112132141 112197677).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 112132141 ≤ 112164909)
    (by decide : 112164909 ≤ 112197677) block2 block3

theorem join_1_0 : (twinPrimeSegment 112066605 112197677).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 112066605 ≤ 112132141)
    (by decide : 112132141 ≤ 112197677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 112066605 112197677).card = 489 := join_1_0

end S053C07
end Sude.GeneratedTwinScan
