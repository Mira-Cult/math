import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S043C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90832941 90865709 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 90832941 90865709).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90832941 90865709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90865709 90898477 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 90865709 90898477).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90865709 90898477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90898477 90931245 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 90898477 90931245).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90898477 90931245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90931245 90964013 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 90931245 90964013).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90931245 90964013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 90832941 90898477).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 90832941 ≤ 90865709)
    (by decide : 90865709 ≤ 90898477) block0 block1

theorem join_0_1 : (twinPrimeSegment 90898477 90964013).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 90898477 ≤ 90931245)
    (by decide : 90931245 ≤ 90964013) block2 block3

theorem join_1_0 : (twinPrimeSegment 90832941 90964013).card = 506 := by
  simpa using combineTwinPrimeSegments (by decide : 90832941 ≤ 90898477)
    (by decide : 90898477 ≤ 90964013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 90832941 90964013).card = 506 := join_1_0

end S043C05
end Sude.GeneratedTwinScan
