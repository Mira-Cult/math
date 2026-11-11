import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S031C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66715693 66748461 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 66715693 66748461).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66715693 66748461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66748461 66781229 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 66748461 66781229).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66748461 66781229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66781229 66813997 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 66781229 66813997).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66781229 66813997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66813997 66846765 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 66813997 66846765).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66813997 66846765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 66715693 66781229).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 66715693 ≤ 66748461)
    (by decide : 66748461 ≤ 66781229) block0 block1

theorem join_0_1 : (twinPrimeSegment 66781229 66846765).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 66781229 ≤ 66813997)
    (by decide : 66813997 ≤ 66846765) block2 block3

theorem join_1_0 : (twinPrimeSegment 66715693 66846765).card = 519 := by
  simpa using combineTwinPrimeSegments (by decide : 66715693 ≤ 66781229)
    (by decide : 66781229 ≤ 66846765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 66715693 66846765).card = 519 := join_1_0

end S031C13
end Sude.GeneratedTwinScan
