import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S036C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76677165 76709933 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 76677165 76709933).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76677165 76709933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76709933 76742701 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 76709933 76742701).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76709933 76742701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76742701 76775469 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 76742701 76775469).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76742701 76775469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76775469 76808237 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 76775469 76808237).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76775469 76808237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 76677165 76742701).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 76677165 ≤ 76709933)
    (by decide : 76709933 ≤ 76742701) block0 block1

theorem join_0_1 : (twinPrimeSegment 76742701 76808237).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 76742701 ≤ 76775469)
    (by decide : 76775469 ≤ 76808237) block2 block3

theorem join_1_0 : (twinPrimeSegment 76677165 76808237).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 76677165 ≤ 76742701)
    (by decide : 76742701 ≤ 76808237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 76677165 76808237).card = 504 := join_1_0

end S036C09
end Sude.GeneratedTwinScan
