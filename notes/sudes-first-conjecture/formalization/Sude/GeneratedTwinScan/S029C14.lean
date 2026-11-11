import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S029C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62652461 62685229 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 62652461 62685229).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62652461 62685229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62685229 62717997 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 62685229 62717997).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62685229 62717997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62717997 62750765 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 62717997 62750765).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62717997 62750765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62750765 62783533 = 160 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 62750765 62783533).card = 160 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62750765 62783533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 62652461 62717997).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 62652461 ≤ 62685229)
    (by decide : 62685229 ≤ 62717997) block0 block1

theorem join_0_1 : (twinPrimeSegment 62717997 62783533).card = 295 := by
  simpa using combineTwinPrimeSegments (by decide : 62717997 ≤ 62750765)
    (by decide : 62750765 ≤ 62783533) block2 block3

theorem join_1_0 : (twinPrimeSegment 62652461 62783533).card = 554 := by
  simpa using combineTwinPrimeSegments (by decide : 62652461 ≤ 62717997)
    (by decide : 62717997 ≤ 62783533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 62652461 62783533).card = 554 := join_1_0

end S029C14
end Sude.GeneratedTwinScan
