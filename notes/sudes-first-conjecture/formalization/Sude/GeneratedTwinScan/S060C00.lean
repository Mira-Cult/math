import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S060C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125829165 125861933 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 125829165 125861933).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125829165 125861933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125861933 125894701 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 125861933 125894701).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125861933 125894701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125894701 125927469 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 125894701 125927469).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125894701 125927469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125927469 125960237 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 125927469 125960237).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125927469 125960237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 125829165 125894701).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 125829165 ≤ 125861933)
    (by decide : 125861933 ≤ 125894701) block0 block1

theorem join_0_1 : (twinPrimeSegment 125894701 125960237).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 125894701 ≤ 125927469)
    (by decide : 125927469 ≤ 125960237) block2 block3

theorem join_1_0 : (twinPrimeSegment 125829165 125960237).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 125829165 ≤ 125894701)
    (by decide : 125894701 ≤ 125960237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 125829165 125960237).card = 491 := join_1_0

end S060C00
end Sude.GeneratedTwinScan
