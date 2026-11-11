import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S047C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99483693 99516461 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 99483693 99516461).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99483693 99516461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99516461 99549229 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 99516461 99549229).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99516461 99549229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99549229 99581997 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 99549229 99581997).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99549229 99581997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99581997 99614765 = 143 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 99581997 99614765).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99581997 99614765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 99483693 99549229).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 99483693 ≤ 99516461)
    (by decide : 99516461 ≤ 99549229) block0 block1

theorem join_0_1 : (twinPrimeSegment 99549229 99614765).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 99549229 ≤ 99581997)
    (by decide : 99581997 ≤ 99614765) block2 block3

theorem join_1_0 : (twinPrimeSegment 99483693 99614765).card = 524 := by
  simpa using combineTwinPrimeSegments (by decide : 99483693 ≤ 99549229)
    (by decide : 99549229 ≤ 99614765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 99483693 99614765).card = 524 := join_1_0

end S047C07
end Sude.GeneratedTwinScan
