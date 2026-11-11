import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S067C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140509229 140541997 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 140509229 140541997).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140509229 140541997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140541997 140574765 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 140541997 140574765).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140541997 140574765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140574765 140607533 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 140574765 140607533).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140574765 140607533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 140607533 140640301 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 140607533 140640301).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 140607533 140640301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 140509229 140574765).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 140509229 ≤ 140541997)
    (by decide : 140541997 ≤ 140574765) block0 block1

theorem join_0_1 : (twinPrimeSegment 140574765 140640301).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 140574765 ≤ 140607533)
    (by decide : 140607533 ≤ 140640301) block2 block3

theorem join_1_0 : (twinPrimeSegment 140509229 140640301).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 140509229 ≤ 140574765)
    (by decide : 140574765 ≤ 140640301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 140509229 140640301).card = 488 := join_1_0

end S067C00
end Sude.GeneratedTwinScan
