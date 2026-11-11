import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S030C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63701037 63733805 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 63701037 63733805).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63701037 63733805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63733805 63766573 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 63733805 63766573).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63733805 63766573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63766573 63799341 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 63766573 63799341).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63766573 63799341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63799341 63832109 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 63799341 63832109).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63799341 63832109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 63701037 63766573).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 63701037 ≤ 63733805)
    (by decide : 63733805 ≤ 63766573) block0 block1

theorem join_0_1 : (twinPrimeSegment 63766573 63832109).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 63766573 ≤ 63799341)
    (by decide : 63799341 ≤ 63832109) block2 block3

theorem join_1_0 : (twinPrimeSegment 63701037 63832109).card = 541 := by
  simpa using combineTwinPrimeSegments (by decide : 63701037 ≤ 63766573)
    (by decide : 63766573 ≤ 63832109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 63701037 63832109).card = 541 := join_1_0

end S030C06
end Sude.GeneratedTwinScan
