import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S039C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83099693 83132461 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 83099693 83132461).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83099693 83132461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83132461 83165229 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 83132461 83165229).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83132461 83165229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83165229 83197997 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 83165229 83197997).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83165229 83197997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83197997 83230765 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 83197997 83230765).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83197997 83230765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 83099693 83165229).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 83099693 ≤ 83132461)
    (by decide : 83132461 ≤ 83165229) block0 block1

theorem join_0_1 : (twinPrimeSegment 83165229 83230765).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 83165229 ≤ 83197997)
    (by decide : 83197997 ≤ 83230765) block2 block3

theorem join_1_0 : (twinPrimeSegment 83099693 83230765).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 83099693 ≤ 83165229)
    (by decide : 83165229 ≤ 83230765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 83099693 83230765).card = 473 := join_1_0

end S039C10
end Sude.GeneratedTwinScan
