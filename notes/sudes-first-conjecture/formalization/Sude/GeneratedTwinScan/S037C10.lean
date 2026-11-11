import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S037C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78905389 78938157 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 78905389 78938157).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78905389 78938157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78938157 78970925 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 78938157 78970925).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78938157 78970925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 78970925 79003693 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 78970925 79003693).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 78970925 79003693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79003693 79036461 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 79003693 79036461).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79003693 79036461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 78905389 78970925).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 78905389 ≤ 78938157)
    (by decide : 78938157 ≤ 78970925) block0 block1

theorem join_0_1 : (twinPrimeSegment 78970925 79036461).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 78970925 ≤ 79003693)
    (by decide : 79003693 ≤ 79036461) block2 block3

theorem join_1_0 : (twinPrimeSegment 78905389 79036461).card = 513 := by
  simpa using combineTwinPrimeSegments (by decide : 78905389 ≤ 78970925)
    (by decide : 78970925 ≤ 79036461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 78905389 79036461).card = 513 := join_1_0

end S037C10
end Sude.GeneratedTwinScan
