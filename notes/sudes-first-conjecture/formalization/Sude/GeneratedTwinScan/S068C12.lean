import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S068C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144179245 144212013 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 144179245 144212013).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144179245 144212013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144212013 144244781 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 144212013 144244781).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144212013 144244781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144244781 144277549 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 144244781 144277549).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144244781 144277549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 144277549 144310317 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 144277549 144310317).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 144277549 144310317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 144179245 144244781).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 144179245 ≤ 144212013)
    (by decide : 144212013 ≤ 144244781) block0 block1

theorem join_0_1 : (twinPrimeSegment 144244781 144310317).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 144244781 ≤ 144277549)
    (by decide : 144277549 ≤ 144310317) block2 block3

theorem join_1_0 : (twinPrimeSegment 144179245 144310317).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 144179245 ≤ 144244781)
    (by decide : 144244781 ≤ 144310317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 144179245 144310317).card = 501 := join_1_0

end S068C12
end Sude.GeneratedTwinScan
