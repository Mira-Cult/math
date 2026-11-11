import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S032C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67633197 67665965 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 67633197 67665965).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67633197 67665965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67665965 67698733 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 67665965 67698733).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67665965 67698733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67698733 67731501 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 67698733 67731501).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67698733 67731501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67731501 67764269 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 67731501 67764269).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67731501 67764269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 67633197 67698733).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 67633197 ≤ 67665965)
    (by decide : 67665965 ≤ 67698733) block0 block1

theorem join_0_1 : (twinPrimeSegment 67698733 67764269).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 67698733 ≤ 67731501)
    (by decide : 67731501 ≤ 67764269) block2 block3

theorem join_1_0 : (twinPrimeSegment 67633197 67764269).card = 543 := by
  simpa using combineTwinPrimeSegments (by decide : 67633197 ≤ 67698733)
    (by decide : 67698733 ≤ 67764269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 67633197 67764269).card = 543 := join_1_0

end S032C04
end Sude.GeneratedTwinScan
