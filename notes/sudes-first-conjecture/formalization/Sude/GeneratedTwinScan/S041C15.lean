import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S041C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87949357 87982125 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 87949357 87982125).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87949357 87982125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87982125 88014893 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 87982125 88014893).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87982125 88014893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88014893 88047661 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 88014893 88047661).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88014893 88047661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88047661 88080429 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 88047661 88080429).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88047661 88080429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 87949357 88014893).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 87949357 ≤ 87982125)
    (by decide : 87982125 ≤ 88014893) block0 block1

theorem join_0_1 : (twinPrimeSegment 88014893 88080429).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 88014893 ≤ 88047661)
    (by decide : 88047661 ≤ 88080429) block2 block3

theorem join_1_0 : (twinPrimeSegment 87949357 88080429).card = 522 := by
  simpa using combineTwinPrimeSegments (by decide : 87949357 ≤ 88014893)
    (by decide : 88014893 ≤ 88080429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 87949357 88080429).card = 522 := join_1_0

end S041C15
end Sude.GeneratedTwinScan
