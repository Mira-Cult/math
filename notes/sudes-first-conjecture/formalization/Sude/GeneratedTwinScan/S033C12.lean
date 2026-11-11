import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S033C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70778925 70811693 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 70778925 70811693).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70778925 70811693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70811693 70844461 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 70811693 70844461).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70811693 70844461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70844461 70877229 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 70844461 70877229).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70844461 70877229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70877229 70909997 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 70877229 70909997).card = 101 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70877229 70909997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 70778925 70844461).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 70778925 ≤ 70811693)
    (by decide : 70811693 ≤ 70844461) block0 block1

theorem join_0_1 : (twinPrimeSegment 70844461 70909997).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 70844461 ≤ 70877229)
    (by decide : 70877229 ≤ 70909997) block2 block3

theorem join_1_0 : (twinPrimeSegment 70778925 70909997).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 70778925 ≤ 70844461)
    (by decide : 70844461 ≤ 70909997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 70778925 70909997).card = 450 := join_1_0

end S033C12
end Sude.GeneratedTwinScan
