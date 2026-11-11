import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S051C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108789805 108822573 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 108789805 108822573).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108789805 108822573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108822573 108855341 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 108822573 108855341).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108822573 108855341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108855341 108888109 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 108855341 108888109).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108855341 108888109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108888109 108920877 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 108888109 108920877).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108888109 108920877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 108789805 108855341).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 108789805 ≤ 108822573)
    (by decide : 108822573 ≤ 108855341) block0 block1

theorem join_0_1 : (twinPrimeSegment 108855341 108920877).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 108855341 ≤ 108888109)
    (by decide : 108888109 ≤ 108920877) block2 block3

theorem join_1_0 : (twinPrimeSegment 108789805 108920877).card = 527 := by
  simpa using combineTwinPrimeSegments (by decide : 108789805 ≤ 108855341)
    (by decide : 108855341 ≤ 108920877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 108789805 108920877).card = 527 := join_1_0

end S051C14
end Sude.GeneratedTwinScan
