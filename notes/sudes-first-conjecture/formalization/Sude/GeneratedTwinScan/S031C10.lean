import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S031C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66322477 66355245 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 66322477 66355245).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66322477 66355245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66355245 66388013 = 147 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 66355245 66388013).card = 147 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66355245 66388013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66388013 66420781 = 149 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 66388013 66420781).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66388013 66420781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66420781 66453549 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 66420781 66453549).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66420781 66453549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 66322477 66388013).card = 281 := by
  simpa using combineTwinPrimeSegments (by decide : 66322477 ≤ 66355245)
    (by decide : 66355245 ≤ 66388013) block0 block1

theorem join_0_1 : (twinPrimeSegment 66388013 66453549).card = 289 := by
  simpa using combineTwinPrimeSegments (by decide : 66388013 ≤ 66420781)
    (by decide : 66420781 ≤ 66453549) block2 block3

theorem join_1_0 : (twinPrimeSegment 66322477 66453549).card = 570 := by
  simpa using combineTwinPrimeSegments (by decide : 66322477 ≤ 66388013)
    (by decide : 66388013 ≤ 66453549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 66322477 66453549).card = 570 := join_1_0

end S031C10
end Sude.GeneratedTwinScan
