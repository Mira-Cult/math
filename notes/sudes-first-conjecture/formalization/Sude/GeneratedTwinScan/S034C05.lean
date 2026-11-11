import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S034C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71958573 71991341 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 71958573 71991341).card = 105 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71958573 71991341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71991341 72024109 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 71991341 72024109).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71991341 72024109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72024109 72056877 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 72024109 72056877).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72024109 72056877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72056877 72089645 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 72056877 72089645).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72056877 72089645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 71958573 72024109).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 71958573 ≤ 71991341)
    (by decide : 71991341 ≤ 72024109) block0 block1

theorem join_0_1 : (twinPrimeSegment 72024109 72089645).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 72024109 ≤ 72056877)
    (by decide : 72056877 ≤ 72089645) block2 block3

theorem join_1_0 : (twinPrimeSegment 71958573 72089645).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 71958573 ≤ 72024109)
    (by decide : 72024109 ≤ 72089645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 71958573 72089645).card = 489 := join_1_0

end S034C05
end Sude.GeneratedTwinScan
