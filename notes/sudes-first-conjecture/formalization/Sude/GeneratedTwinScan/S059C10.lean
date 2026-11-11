import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S059C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125042733 125075501 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 125042733 125075501).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125042733 125075501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125075501 125108269 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 125075501 125108269).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125075501 125108269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125108269 125141037 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 125108269 125141037).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125108269 125141037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125141037 125173805 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 125141037 125173805).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125141037 125173805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 125042733 125108269).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 125042733 ≤ 125075501)
    (by decide : 125075501 ≤ 125108269) block0 block1

theorem join_0_1 : (twinPrimeSegment 125108269 125173805).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 125108269 ≤ 125141037)
    (by decide : 125141037 ≤ 125173805) block2 block3

theorem join_1_0 : (twinPrimeSegment 125042733 125173805).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 125042733 ≤ 125108269)
    (by decide : 125108269 ≤ 125173805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 125042733 125173805).card = 475 := join_1_0

end S059C10
end Sude.GeneratedTwinScan
