import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S058C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122552365 122585133 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 122552365 122585133).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122552365 122585133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122585133 122617901 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 122585133 122617901).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122585133 122617901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122617901 122650669 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 122617901 122650669).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122617901 122650669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122650669 122683437 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 122650669 122683437).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122650669 122683437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 122552365 122617901).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 122552365 ≤ 122585133)
    (by decide : 122585133 ≤ 122617901) block0 block1

theorem join_0_1 : (twinPrimeSegment 122617901 122683437).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 122617901 ≤ 122650669)
    (by decide : 122650669 ≤ 122683437) block2 block3

theorem join_1_0 : (twinPrimeSegment 122552365 122683437).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 122552365 ≤ 122617901)
    (by decide : 122617901 ≤ 122683437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 122552365 122683437).card = 501 := join_1_0

end S058C07
end Sude.GeneratedTwinScan
