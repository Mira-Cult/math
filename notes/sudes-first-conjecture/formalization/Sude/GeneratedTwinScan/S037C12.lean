import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S037C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79167533 79200301 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 79167533 79200301).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79167533 79200301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79200301 79233069 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 79200301 79233069).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79200301 79233069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79233069 79265837 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 79233069 79265837).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79233069 79265837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79265837 79298605 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 79265837 79298605).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79265837 79298605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 79167533 79233069).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 79167533 ≤ 79200301)
    (by decide : 79200301 ≤ 79233069) block0 block1

theorem join_0_1 : (twinPrimeSegment 79233069 79298605).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 79233069 ≤ 79265837)
    (by decide : 79265837 ≤ 79298605) block2 block3

theorem join_1_0 : (twinPrimeSegment 79167533 79298605).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 79167533 ≤ 79233069)
    (by decide : 79233069 ≤ 79298605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 79167533 79298605).card = 494 := join_1_0

end S037C12
end Sude.GeneratedTwinScan
