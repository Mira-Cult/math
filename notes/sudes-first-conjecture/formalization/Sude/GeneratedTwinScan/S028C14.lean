import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S028C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60555309 60588077 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 60555309 60588077).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60555309 60588077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60588077 60620845 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 60588077 60620845).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60588077 60620845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60620845 60653613 = 147 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 60620845 60653613).card = 147 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60620845 60653613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60653613 60686381 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 60653613 60686381).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60653613 60686381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 60555309 60620845).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 60555309 ≤ 60588077)
    (by decide : 60588077 ≤ 60620845) block0 block1

theorem join_0_1 : (twinPrimeSegment 60620845 60686381).card = 275 := by
  simpa using combineTwinPrimeSegments (by decide : 60620845 ≤ 60653613)
    (by decide : 60653613 ≤ 60686381) block2 block3

theorem join_1_0 : (twinPrimeSegment 60555309 60686381).card = 549 := by
  simpa using combineTwinPrimeSegments (by decide : 60555309 ≤ 60620845)
    (by decide : 60620845 ≤ 60686381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 60555309 60686381).card = 549 := join_1_0

end S028C14
end Sude.GeneratedTwinScan
