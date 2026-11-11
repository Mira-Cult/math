import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S068C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144441389 144474157 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 144441389 144474157).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144441389 144474157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144474157 144506925 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 144474157 144506925).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144474157 144506925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144506925 144539693 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 144506925 144539693).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144506925 144539693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144539693 144572461 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 144539693 144572461).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144539693 144572461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 144441389 144506925).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 144441389 ≤ 144474157)
    (by decide : 144474157 ≤ 144506925) block0 block1

theorem join_0_1 : (twinPrimeSegment 144506925 144572461).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 144506925 ≤ 144539693)
    (by decide : 144539693 ≤ 144572461) block2 block3

theorem join_1_0 : (twinPrimeSegment 144441389 144572461).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 144441389 ≤ 144506925)
    (by decide : 144506925 ≤ 144572461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 144441389 144572461).card = 481 := join_1_0

end S068C14
end Sude.GeneratedTwinScan
