import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S068C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143261741 143294509 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 143261741 143294509).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143261741 143294509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143294509 143327277 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 143294509 143327277).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143294509 143327277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143327277 143360045 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 143327277 143360045).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143327277 143360045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143360045 143392813 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 143360045 143392813).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143360045 143392813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 143261741 143327277).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 143261741 ≤ 143294509)
    (by decide : 143294509 ≤ 143327277) block0 block1

theorem join_0_1 : (twinPrimeSegment 143327277 143392813).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 143327277 ≤ 143360045)
    (by decide : 143360045 ≤ 143392813) block2 block3

theorem join_1_0 : (twinPrimeSegment 143261741 143392813).card = 532 := by
  simpa using combineTwinPrimeSegments (by decide : 143261741 ≤ 143327277)
    (by decide : 143327277 ≤ 143392813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 143261741 143392813).card = 532 := join_1_0

end S068C05
end Sude.GeneratedTwinScan
