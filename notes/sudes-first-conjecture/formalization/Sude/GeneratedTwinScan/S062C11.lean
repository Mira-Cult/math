import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S062C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131465261 131498029 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 131465261 131498029).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131465261 131498029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131498029 131530797 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 131498029 131530797).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131498029 131530797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131530797 131563565 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 131530797 131563565).card = 106 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131530797 131563565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 131563565 131596333 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 131563565 131596333).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 131563565 131596333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 131465261 131530797).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 131465261 ≤ 131498029)
    (by decide : 131498029 ≤ 131530797) block0 block1

theorem join_0_1 : (twinPrimeSegment 131530797 131596333).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 131530797 ≤ 131563565)
    (by decide : 131563565 ≤ 131596333) block2 block3

theorem join_1_0 : (twinPrimeSegment 131465261 131596333).card = 498 := by
  simpa using combineTwinPrimeSegments (by decide : 131465261 ≤ 131530797)
    (by decide : 131530797 ≤ 131596333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 131465261 131596333).card = 498 := join_1_0

end S062C11
end Sude.GeneratedTwinScan
