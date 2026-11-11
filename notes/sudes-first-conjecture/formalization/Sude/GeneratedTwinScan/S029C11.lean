import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S029C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62259245 62292013 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 62259245 62292013).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62259245 62292013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62292013 62324781 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 62292013 62324781).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62292013 62324781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62324781 62357549 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 62324781 62357549).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62324781 62357549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62357549 62390317 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 62357549 62390317).card = 105 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62357549 62390317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 62259245 62324781).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 62259245 ≤ 62292013)
    (by decide : 62292013 ≤ 62324781) block0 block1

theorem join_0_1 : (twinPrimeSegment 62324781 62390317).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 62324781 ≤ 62357549)
    (by decide : 62357549 ≤ 62390317) block2 block3

theorem join_1_0 : (twinPrimeSegment 62259245 62390317).card = 511 := by
  simpa using combineTwinPrimeSegments (by decide : 62259245 ≤ 62324781)
    (by decide : 62324781 ≤ 62390317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 62259245 62390317).card = 511 := join_1_0

end S029C11
end Sude.GeneratedTwinScan
