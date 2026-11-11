import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S032C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68288557 68321325 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 68288557 68321325).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68288557 68321325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68321325 68354093 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 68321325 68354093).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68321325 68354093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68354093 68386861 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 68354093 68386861).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68354093 68386861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68386861 68419629 = 147 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 68386861 68419629).card = 147 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68386861 68419629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 68288557 68354093).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 68288557 ≤ 68321325)
    (by decide : 68321325 ≤ 68354093) block0 block1

theorem join_0_1 : (twinPrimeSegment 68354093 68419629).card = 281 := by
  simpa using combineTwinPrimeSegments (by decide : 68354093 ≤ 68386861)
    (by decide : 68386861 ≤ 68419629) block2 block3

theorem join_1_0 : (twinPrimeSegment 68288557 68419629).card = 549 := by
  simpa using combineTwinPrimeSegments (by decide : 68288557 ≤ 68354093)
    (by decide : 68354093 ≤ 68419629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 68288557 68419629).card = 549 := join_1_0

end S032C09
end Sude.GeneratedTwinScan
