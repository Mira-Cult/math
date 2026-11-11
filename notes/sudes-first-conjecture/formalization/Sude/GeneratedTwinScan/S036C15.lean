import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S036C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77463597 77496365 = 151 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 77463597 77496365).card = 151 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77463597 77496365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77496365 77529133 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 77496365 77529133).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77496365 77529133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77529133 77561901 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 77529133 77561901).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77529133 77561901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77561901 77594669 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 77561901 77594669).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77561901 77594669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 77463597 77529133).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 77463597 ≤ 77496365)
    (by decide : 77496365 ≤ 77529133) block0 block1

theorem join_0_1 : (twinPrimeSegment 77529133 77594669).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 77529133 ≤ 77561901)
    (by decide : 77561901 ≤ 77594669) block2 block3

theorem join_1_0 : (twinPrimeSegment 77463597 77594669).card = 527 := by
  simpa using combineTwinPrimeSegments (by decide : 77463597 ≤ 77529133)
    (by decide : 77529133 ≤ 77594669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 77463597 77594669).card = 527 := join_1_0

end S036C15
end Sude.GeneratedTwinScan
