import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S072C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152043565 152076333 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 152043565 152076333).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152043565 152076333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152076333 152109101 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 152076333 152109101).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152076333 152109101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152109101 152141869 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 152109101 152141869).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152109101 152141869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152141869 152174637 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 152141869 152174637).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152141869 152174637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 152043565 152109101).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 152043565 ≤ 152076333)
    (by decide : 152076333 ≤ 152109101) block0 block1

theorem join_0_1 : (twinPrimeSegment 152109101 152174637).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 152109101 ≤ 152141869)
    (by decide : 152141869 ≤ 152174637) block2 block3

theorem join_1_0 : (twinPrimeSegment 152043565 152174637).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 152043565 ≤ 152109101)
    (by decide : 152109101 ≤ 152174637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 152043565 152174637).card = 486 := join_1_0

end S072C08
end Sude.GeneratedTwinScan
