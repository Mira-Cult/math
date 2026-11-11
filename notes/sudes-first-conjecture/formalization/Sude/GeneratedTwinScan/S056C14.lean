import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S056C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119275565 119308333 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 119275565 119308333).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119275565 119308333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119308333 119341101 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 119308333 119341101).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119308333 119341101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119341101 119373869 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 119341101 119373869).card = 102 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119341101 119373869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119373869 119406637 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 119373869 119406637).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119373869 119406637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 119275565 119341101).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 119275565 ≤ 119308333)
    (by decide : 119308333 ≤ 119341101) block0 block1

theorem join_0_1 : (twinPrimeSegment 119341101 119406637).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 119341101 ≤ 119373869)
    (by decide : 119373869 ≤ 119406637) block2 block3

theorem join_1_0 : (twinPrimeSegment 119275565 119406637).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 119275565 ≤ 119341101)
    (by decide : 119341101 ≤ 119406637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 119275565 119406637).card = 477 := join_1_0

end S056C14
end Sude.GeneratedTwinScan
