import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S057C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119537709 119570477 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 119537709 119570477).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119537709 119570477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119570477 119603245 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 119570477 119603245).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119570477 119603245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119603245 119636013 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 119603245 119636013).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119603245 119636013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119636013 119668781 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 119636013 119668781).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119636013 119668781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 119537709 119603245).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 119537709 ≤ 119570477)
    (by decide : 119570477 ≤ 119603245) block0 block1

theorem join_0_1 : (twinPrimeSegment 119603245 119668781).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 119603245 ≤ 119636013)
    (by decide : 119636013 ≤ 119668781) block2 block3

theorem join_1_0 : (twinPrimeSegment 119537709 119668781).card = 503 := by
  simpa using combineTwinPrimeSegments (by decide : 119537709 ≤ 119603245)
    (by decide : 119603245 ≤ 119668781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 119537709 119668781).card = 503 := join_1_0

end S057C00
end Sude.GeneratedTwinScan
