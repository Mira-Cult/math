import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S056C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117702701 117735469 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 117702701 117735469).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117702701 117735469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117735469 117768237 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 117735469 117768237).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117735469 117768237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117768237 117801005 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 117768237 117801005).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117768237 117801005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117801005 117833773 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 117801005 117833773).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117801005 117833773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 117702701 117768237).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 117702701 ≤ 117735469)
    (by decide : 117735469 ≤ 117768237) block0 block1

theorem join_0_1 : (twinPrimeSegment 117768237 117833773).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 117768237 ≤ 117801005)
    (by decide : 117801005 ≤ 117833773) block2 block3

theorem join_1_0 : (twinPrimeSegment 117702701 117833773).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 117702701 ≤ 117768237)
    (by decide : 117768237 ≤ 117833773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 117702701 117833773).card = 485 := join_1_0

end S056C02
end Sude.GeneratedTwinScan
