import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S038C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81526829 81559597 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 81526829 81559597).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81526829 81559597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81559597 81592365 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 81559597 81592365).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81559597 81592365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81592365 81625133 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 81592365 81625133).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81592365 81625133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81625133 81657901 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 81625133 81657901).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81625133 81657901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 81526829 81592365).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 81526829 ≤ 81559597)
    (by decide : 81559597 ≤ 81592365) block0 block1

theorem join_0_1 : (twinPrimeSegment 81592365 81657901).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 81592365 ≤ 81625133)
    (by decide : 81625133 ≤ 81657901) block2 block3

theorem join_1_0 : (twinPrimeSegment 81526829 81657901).card = 525 := by
  simpa using combineTwinPrimeSegments (by decide : 81526829 ≤ 81592365)
    (by decide : 81592365 ≤ 81657901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 81526829 81657901).card = 525 := join_1_0

end S038C14
end Sude.GeneratedTwinScan
