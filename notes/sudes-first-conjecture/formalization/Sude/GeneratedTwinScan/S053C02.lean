import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S053C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111411245 111444013 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 111411245 111444013).card = 98 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111411245 111444013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111444013 111476781 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 111444013 111476781).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111444013 111476781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111476781 111509549 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 111476781 111509549).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111476781 111509549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111509549 111542317 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 111509549 111542317).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111509549 111542317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 111411245 111476781).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 111411245 ≤ 111444013)
    (by decide : 111444013 ≤ 111476781) block0 block1

theorem join_0_1 : (twinPrimeSegment 111476781 111542317).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 111476781 ≤ 111509549)
    (by decide : 111509549 ≤ 111542317) block2 block3

theorem join_1_0 : (twinPrimeSegment 111411245 111542317).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 111411245 ≤ 111476781)
    (by decide : 111476781 ≤ 111542317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 111411245 111542317).card = 484 := join_1_0

end S053C02
end Sude.GeneratedTwinScan
