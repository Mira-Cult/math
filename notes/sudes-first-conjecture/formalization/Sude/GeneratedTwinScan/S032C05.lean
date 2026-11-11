import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S032C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67764269 67797037 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 67764269 67797037).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67764269 67797037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67797037 67829805 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 67797037 67829805).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67797037 67829805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67829805 67862573 = 142 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 67829805 67862573).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67829805 67862573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67862573 67895341 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 67862573 67895341).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67862573 67895341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 67764269 67829805).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 67764269 ≤ 67797037)
    (by decide : 67797037 ≤ 67829805) block0 block1

theorem join_0_1 : (twinPrimeSegment 67829805 67895341).card = 275 := by
  simpa using combineTwinPrimeSegments (by decide : 67829805 ≤ 67862573)
    (by decide : 67862573 ≤ 67895341) block2 block3

theorem join_1_0 : (twinPrimeSegment 67764269 67895341).card = 534 := by
  simpa using combineTwinPrimeSegments (by decide : 67764269 ≤ 67829805)
    (by decide : 67829805 ≤ 67895341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 67764269 67895341).card = 534 := join_1_0

end S032C05
end Sude.GeneratedTwinScan
