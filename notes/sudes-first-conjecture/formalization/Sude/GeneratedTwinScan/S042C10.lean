import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S042C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89391149 89423917 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 89391149 89423917).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89391149 89423917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89423917 89456685 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 89423917 89456685).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89423917 89456685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89456685 89489453 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 89456685 89489453).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89456685 89489453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89489453 89522221 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 89489453 89522221).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89489453 89522221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 89391149 89456685).card = 275 := by
  simpa using combineTwinPrimeSegments (by decide : 89391149 ≤ 89423917)
    (by decide : 89423917 ≤ 89456685) block0 block1

theorem join_0_1 : (twinPrimeSegment 89456685 89522221).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 89456685 ≤ 89489453)
    (by decide : 89489453 ≤ 89522221) block2 block3

theorem join_1_0 : (twinPrimeSegment 89391149 89522221).card = 516 := by
  simpa using combineTwinPrimeSegments (by decide : 89391149 ≤ 89456685)
    (by decide : 89456685 ≤ 89522221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 89391149 89522221).card = 516 := join_1_0

end S042C10
end Sude.GeneratedTwinScan
