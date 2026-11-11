import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S056C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118095917 118128685 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 118095917 118128685).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118095917 118128685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118128685 118161453 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 118128685 118161453).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118128685 118161453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118161453 118194221 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 118161453 118194221).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118161453 118194221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 118194221 118226989 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 118194221 118226989).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 118194221 118226989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 118095917 118161453).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 118095917 ≤ 118128685)
    (by decide : 118128685 ≤ 118161453) block0 block1

theorem join_0_1 : (twinPrimeSegment 118161453 118226989).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 118161453 ≤ 118194221)
    (by decide : 118194221 ≤ 118226989) block2 block3

theorem join_1_0 : (twinPrimeSegment 118095917 118226989).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 118095917 ≤ 118161453)
    (by decide : 118161453 ≤ 118226989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 118095917 118226989).card = 489 := join_1_0

end S056C05
end Sude.GeneratedTwinScan
