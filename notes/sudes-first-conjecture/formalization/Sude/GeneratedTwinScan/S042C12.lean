import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S042C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89653293 89686061 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 89653293 89686061).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89653293 89686061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89686061 89718829 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 89686061 89718829).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89686061 89718829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89718829 89751597 = 142 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 89718829 89751597).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89718829 89751597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89751597 89784365 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 89751597 89784365).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89751597 89784365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 89653293 89718829).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 89653293 ≤ 89686061)
    (by decide : 89686061 ≤ 89718829) block0 block1

theorem join_0_1 : (twinPrimeSegment 89718829 89784365).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 89718829 ≤ 89751597)
    (by decide : 89751597 ≤ 89784365) block2 block3

theorem join_1_0 : (twinPrimeSegment 89653293 89784365).card = 543 := by
  simpa using combineTwinPrimeSegments (by decide : 89653293 ≤ 89718829)
    (by decide : 89718829 ≤ 89784365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 89653293 89784365).card = 543 := join_1_0

end S042C12
end Sude.GeneratedTwinScan
