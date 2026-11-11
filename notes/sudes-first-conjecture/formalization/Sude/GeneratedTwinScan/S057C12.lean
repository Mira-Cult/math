import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S057C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121110573 121143341 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 121110573 121143341).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121110573 121143341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121143341 121176109 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 121143341 121176109).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121143341 121176109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121176109 121208877 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 121176109 121208877).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121176109 121208877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121208877 121241645 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 121208877 121241645).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121208877 121241645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 121110573 121176109).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 121110573 ≤ 121143341)
    (by decide : 121143341 ≤ 121176109) block0 block1

theorem join_0_1 : (twinPrimeSegment 121176109 121241645).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 121176109 ≤ 121208877)
    (by decide : 121208877 ≤ 121241645) block2 block3

theorem join_1_0 : (twinPrimeSegment 121110573 121241645).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 121110573 ≤ 121176109)
    (by decide : 121176109 ≤ 121241645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 121110573 121241645).card = 501 := join_1_0

end S057C12
end Sude.GeneratedTwinScan
