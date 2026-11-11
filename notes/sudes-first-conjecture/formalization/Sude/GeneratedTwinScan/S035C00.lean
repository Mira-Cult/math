import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S035C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73400365 73433133 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 73400365 73433133).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73400365 73433133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73433133 73465901 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 73433133 73465901).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73433133 73465901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73465901 73498669 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 73465901 73498669).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73465901 73498669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73498669 73531437 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 73498669 73531437).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73498669 73531437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 73400365 73465901).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 73400365 ≤ 73433133)
    (by decide : 73433133 ≤ 73465901) block0 block1

theorem join_0_1 : (twinPrimeSegment 73465901 73531437).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 73465901 ≤ 73498669)
    (by decide : 73498669 ≤ 73531437) block2 block3

theorem join_1_0 : (twinPrimeSegment 73400365 73531437).card = 520 := by
  simpa using combineTwinPrimeSegments (by decide : 73400365 ≤ 73465901)
    (by decide : 73465901 ≤ 73531437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 73400365 73531437).card = 520 := join_1_0

end S035C00
end Sude.GeneratedTwinScan
