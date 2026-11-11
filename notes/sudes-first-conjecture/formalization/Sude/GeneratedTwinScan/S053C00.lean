import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S053C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111149101 111181869 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 111149101 111181869).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111149101 111181869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111181869 111214637 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 111181869 111214637).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111181869 111214637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111214637 111247405 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 111214637 111247405).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111214637 111247405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111247405 111280173 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 111247405 111280173).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111247405 111280173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 111149101 111214637).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 111149101 ≤ 111181869)
    (by decide : 111181869 ≤ 111214637) block0 block1

theorem join_0_1 : (twinPrimeSegment 111214637 111280173).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 111214637 ≤ 111247405)
    (by decide : 111247405 ≤ 111280173) block2 block3

theorem join_1_0 : (twinPrimeSegment 111149101 111280173).card = 503 := by
  simpa using combineTwinPrimeSegments (by decide : 111149101 ≤ 111214637)
    (by decide : 111214637 ≤ 111280173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 111149101 111280173).card = 503 := join_1_0

end S053C00
end Sude.GeneratedTwinScan
