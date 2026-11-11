import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S033C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69730349 69763117 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 69730349 69763117).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69730349 69763117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69763117 69795885 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 69763117 69795885).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69763117 69795885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69795885 69828653 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 69795885 69828653).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69795885 69828653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69828653 69861421 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 69828653 69861421).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69828653 69861421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 69730349 69795885).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 69730349 ≤ 69763117)
    (by decide : 69763117 ≤ 69795885) block0 block1

theorem join_0_1 : (twinPrimeSegment 69795885 69861421).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 69795885 ≤ 69828653)
    (by decide : 69828653 ≤ 69861421) block2 block3

theorem join_1_0 : (twinPrimeSegment 69730349 69861421).card = 510 := by
  simpa using combineTwinPrimeSegments (by decide : 69730349 ≤ 69795885)
    (by decide : 69795885 ≤ 69861421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 69730349 69861421).card = 510 := join_1_0

end S033C04
end Sude.GeneratedTwinScan
