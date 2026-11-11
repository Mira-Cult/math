import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S052C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109183021 109215789 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 109183021 109215789).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109183021 109215789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109215789 109248557 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 109215789 109248557).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109215789 109248557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109248557 109281325 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 109248557 109281325).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109248557 109281325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109281325 109314093 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 109281325 109314093).card = 102 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109281325 109314093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 109183021 109248557).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 109183021 ≤ 109215789)
    (by decide : 109215789 ≤ 109248557) block0 block1

theorem join_0_1 : (twinPrimeSegment 109248557 109314093).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 109248557 ≤ 109281325)
    (by decide : 109281325 ≤ 109314093) block2 block3

theorem join_1_0 : (twinPrimeSegment 109183021 109314093).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 109183021 ≤ 109248557)
    (by decide : 109248557 ≤ 109314093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 109183021 109314093).card = 491 := join_1_0

end S052C01
end Sude.GeneratedTwinScan
