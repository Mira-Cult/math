import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S056C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117571629 117604397 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 117571629 117604397).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117571629 117604397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117604397 117637165 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 117604397 117637165).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117604397 117637165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117637165 117669933 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 117637165 117669933).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117637165 117669933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117669933 117702701 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 117669933 117702701).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117669933 117702701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 117571629 117637165).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 117571629 ≤ 117604397)
    (by decide : 117604397 ≤ 117637165) block0 block1

theorem join_0_1 : (twinPrimeSegment 117637165 117702701).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 117637165 ≤ 117669933)
    (by decide : 117669933 ≤ 117702701) block2 block3

theorem join_1_0 : (twinPrimeSegment 117571629 117702701).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 117571629 ≤ 117637165)
    (by decide : 117637165 ≤ 117702701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 117571629 117702701).card = 504 := join_1_0

end S056C01
end Sude.GeneratedTwinScan
