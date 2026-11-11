import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S067C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141164589 141197357 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 141164589 141197357).card = 103 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141164589 141197357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141197357 141230125 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 141197357 141230125).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141197357 141230125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141230125 141262893 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 141230125 141262893).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141230125 141262893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141262893 141295661 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 141262893 141295661).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141262893 141295661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 141164589 141230125).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 141164589 ≤ 141197357)
    (by decide : 141197357 ≤ 141230125) block0 block1

theorem join_0_1 : (twinPrimeSegment 141230125 141295661).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 141230125 ≤ 141262893)
    (by decide : 141262893 ≤ 141295661) block2 block3

theorem join_1_0 : (twinPrimeSegment 141164589 141295661).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 141164589 ≤ 141230125)
    (by decide : 141230125 ≤ 141295661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 141164589 141295661).card = 486 := join_1_0

end S067C05
end Sude.GeneratedTwinScan
