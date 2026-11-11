import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S035C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74711085 74743853 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 74711085 74743853).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74711085 74743853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74743853 74776621 = 143 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 74743853 74776621).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74743853 74776621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74776621 74809389 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 74776621 74809389).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74776621 74809389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74809389 74842157 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 74809389 74842157).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74809389 74842157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 74711085 74776621).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 74711085 ≤ 74743853)
    (by decide : 74743853 ≤ 74776621) block0 block1

theorem join_0_1 : (twinPrimeSegment 74776621 74842157).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 74776621 ≤ 74809389)
    (by decide : 74809389 ≤ 74842157) block2 block3

theorem join_1_0 : (twinPrimeSegment 74711085 74842157).card = 511 := by
  simpa using combineTwinPrimeSegments (by decide : 74711085 ≤ 74776621)
    (by decide : 74776621 ≤ 74842157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 74711085 74842157).card = 511 := join_1_0

end S035C10
end Sude.GeneratedTwinScan
