import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S051C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106954797 106987565 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 106954797 106987565).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106954797 106987565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106987565 107020333 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 106987565 107020333).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106987565 107020333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107020333 107053101 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 107020333 107053101).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107020333 107053101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107053101 107085869 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 107053101 107085869).card = 102 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107053101 107085869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 106954797 107020333).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 106954797 ≤ 106987565)
    (by decide : 106987565 ≤ 107020333) block0 block1

theorem join_0_1 : (twinPrimeSegment 107020333 107085869).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 107020333 ≤ 107053101)
    (by decide : 107053101 ≤ 107085869) block2 block3

theorem join_1_0 : (twinPrimeSegment 106954797 107085869).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 106954797 ≤ 107020333)
    (by decide : 107020333 ≤ 107085869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 106954797 107085869).card = 486 := join_1_0

end S051C00
end Sude.GeneratedTwinScan
