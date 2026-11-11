import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S062C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130940973 130973741 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 130940973 130973741).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130940973 130973741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130973741 131006509 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 130973741 131006509).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130973741 131006509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131006509 131039277 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 131006509 131039277).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131006509 131039277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131039277 131072045 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 131039277 131072045).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131039277 131072045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 130940973 131006509).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 130940973 ≤ 130973741)
    (by decide : 130973741 ≤ 131006509) block0 block1

theorem join_0_1 : (twinPrimeSegment 131006509 131072045).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 131006509 ≤ 131039277)
    (by decide : 131039277 ≤ 131072045) block2 block3

theorem join_1_0 : (twinPrimeSegment 130940973 131072045).card = 509 := by
  simpa using combineTwinPrimeSegments (by decide : 130940973 ≤ 131006509)
    (by decide : 131006509 ≤ 131072045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 130940973 131072045).card = 509 := join_1_0

end S062C07
end Sude.GeneratedTwinScan
