import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S033C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70909997 70942765 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 70909997 70942765).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70909997 70942765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70942765 70975533 = 151 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 70942765 70975533).card = 151 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70942765 70975533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70975533 71008301 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 70975533 71008301).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70975533 71008301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71008301 71041069 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 71008301 71041069).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71008301 71041069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 70909997 70975533).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 70909997 ≤ 70942765)
    (by decide : 70942765 ≤ 70975533) block0 block1

theorem join_0_1 : (twinPrimeSegment 70975533 71041069).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 70975533 ≤ 71008301)
    (by decide : 71008301 ≤ 71041069) block2 block3

theorem join_1_0 : (twinPrimeSegment 70909997 71041069).card = 524 := by
  simpa using combineTwinPrimeSegments (by decide : 70909997 ≤ 70975533)
    (by decide : 70975533 ≤ 71041069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 70909997 71041069).card = 524 := join_1_0

end S033C13
end Sude.GeneratedTwinScan
