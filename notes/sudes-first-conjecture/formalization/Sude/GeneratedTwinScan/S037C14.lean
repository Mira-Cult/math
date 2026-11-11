import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S037C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79429677 79462445 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 79429677 79462445).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79429677 79462445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79462445 79495213 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 79462445 79495213).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79462445 79495213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79495213 79527981 = 148 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 79495213 79527981).card = 148 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79495213 79527981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79527981 79560749 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 79527981 79560749).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79527981 79560749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 79429677 79495213).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 79429677 ≤ 79462445)
    (by decide : 79462445 ≤ 79495213) block0 block1

theorem join_0_1 : (twinPrimeSegment 79495213 79560749).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 79495213 ≤ 79527981)
    (by decide : 79527981 ≤ 79560749) block2 block3

theorem join_1_0 : (twinPrimeSegment 79429677 79560749).card = 529 := by
  simpa using combineTwinPrimeSegments (by decide : 79429677 ≤ 79495213)
    (by decide : 79495213 ≤ 79560749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 79429677 79560749).card = 529 := join_1_0

end S037C14
end Sude.GeneratedTwinScan
