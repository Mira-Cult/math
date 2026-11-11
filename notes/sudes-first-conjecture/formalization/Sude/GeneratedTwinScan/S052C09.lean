import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S052C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110231597 110264365 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 110231597 110264365).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110231597 110264365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110264365 110297133 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 110264365 110297133).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110264365 110297133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110297133 110329901 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 110297133 110329901).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110297133 110329901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110329901 110362669 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 110329901 110362669).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110329901 110362669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 110231597 110297133).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 110231597 ≤ 110264365)
    (by decide : 110264365 ≤ 110297133) block0 block1

theorem join_0_1 : (twinPrimeSegment 110297133 110362669).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 110297133 ≤ 110329901)
    (by decide : 110329901 ≤ 110362669) block2 block3

theorem join_1_0 : (twinPrimeSegment 110231597 110362669).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 110231597 ≤ 110297133)
    (by decide : 110297133 ≤ 110362669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 110231597 110362669).card = 489 := join_1_0

end S052C09
end Sude.GeneratedTwinScan
