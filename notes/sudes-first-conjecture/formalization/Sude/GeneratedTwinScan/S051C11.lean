import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S051C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108396589 108429357 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 108396589 108429357).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108396589 108429357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108429357 108462125 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 108429357 108462125).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108429357 108462125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108462125 108494893 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 108462125 108494893).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108462125 108494893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108494893 108527661 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 108494893 108527661).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108494893 108527661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 108396589 108462125).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 108396589 ≤ 108429357)
    (by decide : 108429357 ≤ 108462125) block0 block1

theorem join_0_1 : (twinPrimeSegment 108462125 108527661).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 108462125 ≤ 108494893)
    (by decide : 108494893 ≤ 108527661) block2 block3

theorem join_1_0 : (twinPrimeSegment 108396589 108527661).card = 502 := by
  simpa using combineTwinPrimeSegments (by decide : 108396589 ≤ 108462125)
    (by decide : 108462125 ≤ 108527661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 108396589 108527661).card = 502 := join_1_0

end S051C11
end Sude.GeneratedTwinScan
