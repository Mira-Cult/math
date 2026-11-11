import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S033C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70123565 70156333 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 70123565 70156333).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70123565 70156333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70156333 70189101 = 142 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 70156333 70189101).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70156333 70189101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70189101 70221869 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 70189101 70221869).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70189101 70221869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70221869 70254637 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 70221869 70254637).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70221869 70254637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 70123565 70189101).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 70123565 ≤ 70156333)
    (by decide : 70156333 ≤ 70189101) block0 block1

theorem join_0_1 : (twinPrimeSegment 70189101 70254637).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 70189101 ≤ 70221869)
    (by decide : 70221869 ≤ 70254637) block2 block3

theorem join_1_0 : (twinPrimeSegment 70123565 70254637).card = 527 := by
  simpa using combineTwinPrimeSegments (by decide : 70123565 ≤ 70189101)
    (by decide : 70189101 ≤ 70254637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 70123565 70254637).card = 527 := join_1_0

end S033C07
end Sude.GeneratedTwinScan
