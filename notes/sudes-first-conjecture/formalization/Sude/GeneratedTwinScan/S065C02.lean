import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S065C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136577069 136609837 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 136577069 136609837).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136577069 136609837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136609837 136642605 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 136609837 136642605).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136609837 136642605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136642605 136675373 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 136642605 136675373).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136642605 136675373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136675373 136708141 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 136675373 136708141).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136675373 136708141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 136577069 136642605).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 136577069 ≤ 136609837)
    (by decide : 136609837 ≤ 136642605) block0 block1

theorem join_0_1 : (twinPrimeSegment 136642605 136708141).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 136642605 ≤ 136675373)
    (by decide : 136675373 ≤ 136708141) block2 block3

theorem join_1_0 : (twinPrimeSegment 136577069 136708141).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 136577069 ≤ 136642605)
    (by decide : 136642605 ≤ 136708141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 136577069 136708141).card = 494 := join_1_0

end S065C02
end Sude.GeneratedTwinScan
