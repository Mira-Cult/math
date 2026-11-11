import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S066C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138543149 138575917 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 138543149 138575917).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138543149 138575917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138575917 138608685 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 138575917 138608685).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138575917 138608685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138608685 138641453 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 138608685 138641453).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138608685 138641453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138641453 138674221 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 138641453 138674221).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138641453 138674221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 138543149 138608685).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 138543149 ≤ 138575917)
    (by decide : 138575917 ≤ 138608685) block0 block1

theorem join_0_1 : (twinPrimeSegment 138608685 138674221).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 138608685 ≤ 138641453)
    (by decide : 138641453 ≤ 138674221) block2 block3

theorem join_1_0 : (twinPrimeSegment 138543149 138674221).card = 499 := by
  simpa using combineTwinPrimeSegments (by decide : 138543149 ≤ 138608685)
    (by decide : 138608685 ≤ 138674221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 138543149 138674221).card = 499 := join_1_0

end S066C01
end Sude.GeneratedTwinScan
