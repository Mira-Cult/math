import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S046C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97910829 97943597 = 144 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 97910829 97943597).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97910829 97943597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97943597 97976365 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 97943597 97976365).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97943597 97976365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 97976365 98009133 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 97976365 98009133).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 97976365 98009133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98009133 98041901 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 98009133 98041901).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98009133 98041901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 97910829 97976365).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 97910829 ≤ 97943597)
    (by decide : 97943597 ≤ 97976365) block0 block1

theorem join_0_1 : (twinPrimeSegment 97976365 98041901).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 97976365 ≤ 98009133)
    (by decide : 98009133 ≤ 98041901) block2 block3

theorem join_1_0 : (twinPrimeSegment 97910829 98041901).card = 522 := by
  simpa using combineTwinPrimeSegments (by decide : 97910829 ≤ 97976365)
    (by decide : 97976365 ≤ 98041901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 97910829 98041901).card = 522 := join_1_0

end S046C11
end Sude.GeneratedTwinScan
