import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S042C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89915437 89948205 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 89915437 89948205).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89915437 89948205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89948205 89980973 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 89948205 89980973).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89948205 89980973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89980973 90013741 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 89980973 90013741).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89980973 90013741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 90013741 90046509 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 90013741 90046509).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 90013741 90046509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 89915437 89980973).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 89915437 ≤ 89948205)
    (by decide : 89948205 ≤ 89980973) block0 block1

theorem join_0_1 : (twinPrimeSegment 89980973 90046509).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 89980973 ≤ 90013741)
    (by decide : 90013741 ≤ 90046509) block2 block3

theorem join_1_0 : (twinPrimeSegment 89915437 90046509).card = 521 := by
  simpa using combineTwinPrimeSegments (by decide : 89915437 ≤ 89980973)
    (by decide : 89980973 ≤ 90046509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 89915437 90046509).card = 521 := join_1_0

end S042C14
end Sude.GeneratedTwinScan
