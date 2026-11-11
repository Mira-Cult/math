import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S072C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152305709 152338477 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 152305709 152338477).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152305709 152338477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152338477 152371245 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 152338477 152371245).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152338477 152371245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152371245 152404013 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 152371245 152404013).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152371245 152404013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152404013 152436781 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 152404013 152436781).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152404013 152436781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 152305709 152371245).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 152305709 ≤ 152338477)
    (by decide : 152338477 ≤ 152371245) block0 block1

theorem join_0_1 : (twinPrimeSegment 152371245 152436781).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 152371245 ≤ 152404013)
    (by decide : 152404013 ≤ 152436781) block2 block3

theorem join_1_0 : (twinPrimeSegment 152305709 152436781).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 152305709 ≤ 152371245)
    (by decide : 152371245 ≤ 152436781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 152305709 152436781).card = 485 := join_1_0

end S072C10
end Sude.GeneratedTwinScan
