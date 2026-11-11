import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S037C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79298605 79331373 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 79298605 79331373).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79298605 79331373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79331373 79364141 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 79331373 79364141).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79331373 79364141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79364141 79396909 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 79364141 79396909).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79364141 79396909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79396909 79429677 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 79396909 79429677).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79396909 79429677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 79298605 79364141).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 79298605 ≤ 79331373)
    (by decide : 79331373 ≤ 79364141) block0 block1

theorem join_0_1 : (twinPrimeSegment 79364141 79429677).card = 278 := by
  simpa using combineTwinPrimeSegments (by decide : 79364141 ≤ 79396909)
    (by decide : 79396909 ≤ 79429677) block2 block3

theorem join_1_0 : (twinPrimeSegment 79298605 79429677).card = 534 := by
  simpa using combineTwinPrimeSegments (by decide : 79298605 ≤ 79364141)
    (by decide : 79364141 ≤ 79429677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 79298605 79429677).card = 534 := join_1_0

end S037C13
end Sude.GeneratedTwinScan
