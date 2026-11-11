import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S070C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148242477 148275245 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 148242477 148275245).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148242477 148275245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148275245 148308013 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 148275245 148308013).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148275245 148308013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148308013 148340781 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 148308013 148340781).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148308013 148340781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148340781 148373549 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 148340781 148373549).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148340781 148373549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 148242477 148308013).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 148242477 ≤ 148275245)
    (by decide : 148275245 ≤ 148308013) block0 block1

theorem join_0_1 : (twinPrimeSegment 148308013 148373549).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 148308013 ≤ 148340781)
    (by decide : 148340781 ≤ 148373549) block2 block3

theorem join_1_0 : (twinPrimeSegment 148242477 148373549).card = 503 := by
  simpa using combineTwinPrimeSegments (by decide : 148242477 ≤ 148308013)
    (by decide : 148308013 ≤ 148373549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 148242477 148373549).card = 503 := join_1_0

end S070C11
end Sude.GeneratedTwinScan
