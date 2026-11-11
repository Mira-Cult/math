import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S060C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127795245 127828013 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 127795245 127828013).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127795245 127828013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127828013 127860781 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 127828013 127860781).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127828013 127860781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127860781 127893549 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 127860781 127893549).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127860781 127893549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127893549 127926317 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 127893549 127926317).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127893549 127926317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 127795245 127860781).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 127795245 ≤ 127828013)
    (by decide : 127828013 ≤ 127860781) block0 block1

theorem join_0_1 : (twinPrimeSegment 127860781 127926317).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 127860781 ≤ 127893549)
    (by decide : 127893549 ≤ 127926317) block2 block3

theorem join_1_0 : (twinPrimeSegment 127795245 127926317).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 127795245 ≤ 127860781)
    (by decide : 127860781 ≤ 127926317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 127795245 127926317).card = 471 := join_1_0

end S060C15
end Sude.GeneratedTwinScan
