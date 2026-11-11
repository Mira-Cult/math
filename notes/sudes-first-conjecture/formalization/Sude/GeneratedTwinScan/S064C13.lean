import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S064C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135921709 135954477 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 135921709 135954477).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135921709 135954477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135954477 135987245 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 135954477 135987245).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135954477 135987245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 135987245 136020013 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 135987245 136020013).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 135987245 136020013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136020013 136052781 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 136020013 136052781).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136020013 136052781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 135921709 135987245).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 135921709 ≤ 135954477)
    (by decide : 135954477 ≤ 135987245) block0 block1

theorem join_0_1 : (twinPrimeSegment 135987245 136052781).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 135987245 ≤ 136020013)
    (by decide : 136020013 ≤ 136052781) block2 block3

theorem join_1_0 : (twinPrimeSegment 135921709 136052781).card = 500 := by
  simpa using combineTwinPrimeSegments (by decide : 135921709 ≤ 135987245)
    (by decide : 135987245 ≤ 136052781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 135921709 136052781).card = 500 := join_1_0

end S064C13
end Sude.GeneratedTwinScan
