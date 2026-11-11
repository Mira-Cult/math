import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S037C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79560749 79593517 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 79560749 79593517).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79560749 79593517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79593517 79626285 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 79593517 79626285).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79593517 79626285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79626285 79659053 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 79626285 79659053).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79626285 79659053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79659053 79691821 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 79659053 79691821).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79659053 79691821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 79560749 79626285).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 79560749 ≤ 79593517)
    (by decide : 79593517 ≤ 79626285) block0 block1

theorem join_0_1 : (twinPrimeSegment 79626285 79691821).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 79626285 ≤ 79659053)
    (by decide : 79659053 ≤ 79691821) block2 block3

theorem join_1_0 : (twinPrimeSegment 79560749 79691821).card = 508 := by
  simpa using combineTwinPrimeSegments (by decide : 79560749 ≤ 79626285)
    (by decide : 79626285 ≤ 79691821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 79560749 79691821).card = 508 := join_1_0

end S037C15
end Sude.GeneratedTwinScan
