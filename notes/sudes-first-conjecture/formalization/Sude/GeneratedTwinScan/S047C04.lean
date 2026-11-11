import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S047C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99090477 99123245 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 99090477 99123245).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99090477 99123245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99123245 99156013 = 151 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 99123245 99156013).card = 151 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99123245 99156013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99156013 99188781 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 99156013 99188781).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99156013 99188781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 99188781 99221549 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 99188781 99221549).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 99188781 99221549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 99090477 99156013).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 99090477 ≤ 99123245)
    (by decide : 99123245 ≤ 99156013) block0 block1

theorem join_0_1 : (twinPrimeSegment 99156013 99221549).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 99156013 ≤ 99188781)
    (by decide : 99188781 ≤ 99221549) block2 block3

theorem join_1_0 : (twinPrimeSegment 99090477 99221549).card = 508 := by
  simpa using combineTwinPrimeSegments (by decide : 99090477 ≤ 99156013)
    (by decide : 99156013 ≤ 99221549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 99090477 99221549).card = 508 := join_1_0

end S047C04
end Sude.GeneratedTwinScan
