import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S038C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81002541 81035309 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 81002541 81035309).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81002541 81035309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81035309 81068077 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 81035309 81068077).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81035309 81068077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81068077 81100845 = 146 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 81068077 81100845).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81068077 81100845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 81100845 81133613 = 157 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 81100845 81133613).card = 157 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 81100845 81133613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 81002541 81068077).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 81002541 ≤ 81035309)
    (by decide : 81035309 ≤ 81068077) block0 block1

theorem join_0_1 : (twinPrimeSegment 81068077 81133613).card = 303 := by
  simpa using combineTwinPrimeSegments (by decide : 81068077 ≤ 81100845)
    (by decide : 81100845 ≤ 81133613) block2 block3

theorem join_1_0 : (twinPrimeSegment 81002541 81133613).card = 561 := by
  simpa using combineTwinPrimeSegments (by decide : 81002541 ≤ 81068077)
    (by decide : 81068077 ≤ 81133613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 81002541 81133613).card = 561 := join_1_0

end S038C10
end Sude.GeneratedTwinScan
