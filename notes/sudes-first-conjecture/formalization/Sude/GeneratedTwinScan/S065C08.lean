import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S065C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137363501 137396269 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 137363501 137396269).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137363501 137396269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137396269 137429037 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 137396269 137429037).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137396269 137429037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137429037 137461805 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 137429037 137461805).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137429037 137461805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 137461805 137494573 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 137461805 137494573).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 137461805 137494573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 137363501 137429037).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 137363501 ≤ 137396269)
    (by decide : 137396269 ≤ 137429037) block0 block1

theorem join_0_1 : (twinPrimeSegment 137429037 137494573).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 137429037 ≤ 137461805)
    (by decide : 137461805 ≤ 137494573) block2 block3

theorem join_1_0 : (twinPrimeSegment 137363501 137494573).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 137363501 ≤ 137429037)
    (by decide : 137429037 ≤ 137494573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 137363501 137494573).card = 489 := join_1_0

end S065C08
end Sude.GeneratedTwinScan
