import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S036C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77332525 77365293 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 77332525 77365293).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77332525 77365293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77365293 77398061 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 77365293 77398061).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77365293 77398061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77398061 77430829 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 77398061 77430829).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77398061 77430829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 77430829 77463597 = 147 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 77430829 77463597).card = 147 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 77430829 77463597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 77332525 77398061).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 77332525 ≤ 77365293)
    (by decide : 77365293 ≤ 77398061) block0 block1

theorem join_0_1 : (twinPrimeSegment 77398061 77463597).card = 278 := by
  simpa using combineTwinPrimeSegments (by decide : 77398061 ≤ 77430829)
    (by decide : 77430829 ≤ 77463597) block2 block3

theorem join_1_0 : (twinPrimeSegment 77332525 77463597).card = 528 := by
  simpa using combineTwinPrimeSegments (by decide : 77332525 ≤ 77398061)
    (by decide : 77398061 ≤ 77463597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 77332525 77463597).card = 528 := join_1_0

end S036C14
end Sude.GeneratedTwinScan
