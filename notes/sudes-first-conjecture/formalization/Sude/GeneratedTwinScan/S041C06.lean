import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S041C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86769709 86802477 = 141 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 86769709 86802477).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86769709 86802477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86802477 86835245 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 86802477 86835245).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86802477 86835245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86835245 86868013 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 86835245 86868013).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86835245 86868013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86868013 86900781 = 145 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 86868013 86900781).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86868013 86900781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 86769709 86835245).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 86769709 ≤ 86802477)
    (by decide : 86802477 ≤ 86835245) block0 block1

theorem join_0_1 : (twinPrimeSegment 86835245 86900781).card = 282 := by
  simpa using combineTwinPrimeSegments (by decide : 86835245 ≤ 86868013)
    (by decide : 86868013 ≤ 86900781) block2 block3

theorem join_1_0 : (twinPrimeSegment 86769709 86900781).card = 545 := by
  simpa using combineTwinPrimeSegments (by decide : 86769709 ≤ 86835245)
    (by decide : 86835245 ≤ 86900781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 86769709 86900781).card = 545 := join_1_0

end S041C06
end Sude.GeneratedTwinScan
