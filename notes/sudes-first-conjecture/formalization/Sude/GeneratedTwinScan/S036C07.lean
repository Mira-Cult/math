import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S036C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76415021 76447789 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 76415021 76447789).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76415021 76447789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76447789 76480557 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 76447789 76480557).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76447789 76480557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76480557 76513325 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 76480557 76513325).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76480557 76513325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 76513325 76546093 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 76513325 76546093).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 76513325 76546093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 76415021 76480557).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 76415021 ≤ 76447789)
    (by decide : 76447789 ≤ 76480557) block0 block1

theorem join_0_1 : (twinPrimeSegment 76480557 76546093).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 76480557 ≤ 76513325)
    (by decide : 76513325 ≤ 76546093) block2 block3

theorem join_1_0 : (twinPrimeSegment 76415021 76546093).card = 524 := by
  simpa using combineTwinPrimeSegments (by decide : 76415021 ≤ 76480557)
    (by decide : 76480557 ≤ 76546093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 76415021 76546093).card = 524 := join_1_0

end S036C07
end Sude.GeneratedTwinScan
