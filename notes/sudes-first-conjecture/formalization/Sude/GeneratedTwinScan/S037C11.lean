import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S037C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79036461 79069229 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 79036461 79069229).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79036461 79069229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79069229 79101997 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 79069229 79101997).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79069229 79101997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79101997 79134765 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 79101997 79134765).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79101997 79134765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 79134765 79167533 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 79134765 79167533).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 79134765 79167533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 79036461 79101997).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 79036461 ≤ 79069229)
    (by decide : 79069229 ≤ 79101997) block0 block1

theorem join_0_1 : (twinPrimeSegment 79101997 79167533).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 79101997 ≤ 79134765)
    (by decide : 79134765 ≤ 79167533) block2 block3

theorem join_1_0 : (twinPrimeSegment 79036461 79167533).card = 513 := by
  simpa using combineTwinPrimeSegments (by decide : 79036461 ≤ 79101997)
    (by decide : 79101997 ≤ 79167533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 79036461 79167533).card = 513 := join_1_0

end S037C11
end Sude.GeneratedTwinScan
