import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S049C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103415853 103448621 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 103415853 103448621).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103415853 103448621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103448621 103481389 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 103448621 103481389).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103448621 103481389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103481389 103514157 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 103481389 103514157).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103481389 103514157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103514157 103546925 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 103514157 103546925).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103514157 103546925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 103415853 103481389).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 103415853 ≤ 103448621)
    (by decide : 103448621 ≤ 103481389) block0 block1

theorem join_0_1 : (twinPrimeSegment 103481389 103546925).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 103481389 ≤ 103514157)
    (by decide : 103514157 ≤ 103546925) block2 block3

theorem join_1_0 : (twinPrimeSegment 103415853 103546925).card = 529 := by
  simpa using combineTwinPrimeSegments (by decide : 103415853 ≤ 103481389)
    (by decide : 103481389 ≤ 103546925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 103415853 103546925).card = 529 := join_1_0

end S049C05
end Sude.GeneratedTwinScan
