import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S061C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129237037 129269805 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 129237037 129269805).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129237037 129269805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129269805 129302573 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 129269805 129302573).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129269805 129302573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129302573 129335341 = 147 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 129302573 129335341).card = 147 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129302573 129335341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129335341 129368109 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 129335341 129368109).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129335341 129368109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 129237037 129302573).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 129237037 ≤ 129269805)
    (by decide : 129269805 ≤ 129302573) block0 block1

theorem join_0_1 : (twinPrimeSegment 129302573 129368109).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 129302573 ≤ 129335341)
    (by decide : 129335341 ≤ 129368109) block2 block3

theorem join_1_0 : (twinPrimeSegment 129237037 129368109).card = 518 := by
  simpa using combineTwinPrimeSegments (by decide : 129237037 ≤ 129302573)
    (by decide : 129302573 ≤ 129368109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 129237037 129368109).card = 518 := join_1_0

end S061C10
end Sude.GeneratedTwinScan
