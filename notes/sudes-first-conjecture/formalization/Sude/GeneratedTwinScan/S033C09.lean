import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S033C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70385709 70418477 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 70385709 70418477).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70385709 70418477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70418477 70451245 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 70418477 70451245).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70418477 70451245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70451245 70484013 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 70451245 70484013).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70451245 70484013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70484013 70516781 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 70484013 70516781).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70484013 70516781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 70385709 70451245).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 70385709 ≤ 70418477)
    (by decide : 70418477 ≤ 70451245) block0 block1

theorem join_0_1 : (twinPrimeSegment 70451245 70516781).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 70451245 ≤ 70484013)
    (by decide : 70484013 ≤ 70516781) block2 block3

theorem join_1_0 : (twinPrimeSegment 70385709 70516781).card = 525 := by
  simpa using combineTwinPrimeSegments (by decide : 70385709 ≤ 70451245)
    (by decide : 70451245 ≤ 70516781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 70385709 70516781).card = 525 := join_1_0

end S033C09
end Sude.GeneratedTwinScan
