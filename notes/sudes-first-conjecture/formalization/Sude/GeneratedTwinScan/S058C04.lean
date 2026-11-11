import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S058C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122159149 122191917 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 122159149 122191917).card = 101 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122159149 122191917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122191917 122224685 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 122191917 122224685).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122191917 122224685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122224685 122257453 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 122224685 122257453).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122224685 122257453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 122257453 122290221 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 122257453 122290221).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 122257453 122290221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 122159149 122224685).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 122159149 ≤ 122191917)
    (by decide : 122191917 ≤ 122224685) block0 block1

theorem join_0_1 : (twinPrimeSegment 122224685 122290221).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 122224685 ≤ 122257453)
    (by decide : 122257453 ≤ 122290221) block2 block3

theorem join_1_0 : (twinPrimeSegment 122159149 122290221).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 122159149 ≤ 122224685)
    (by decide : 122224685 ≤ 122290221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 122159149 122290221).card = 449 := join_1_0

end S058C04
end Sude.GeneratedTwinScan
