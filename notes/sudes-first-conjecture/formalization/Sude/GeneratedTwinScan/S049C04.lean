import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S049C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103284781 103317549 = 144 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 103284781 103317549).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103284781 103317549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103317549 103350317 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 103317549 103350317).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103317549 103350317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103350317 103383085 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 103350317 103383085).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103350317 103383085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103383085 103415853 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 103383085 103415853).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103383085 103415853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 103284781 103350317).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 103284781 ≤ 103317549)
    (by decide : 103317549 ≤ 103350317) block0 block1

theorem join_0_1 : (twinPrimeSegment 103350317 103415853).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 103350317 ≤ 103383085)
    (by decide : 103383085 ≤ 103415853) block2 block3

theorem join_1_0 : (twinPrimeSegment 103284781 103415853).card = 528 := by
  simpa using combineTwinPrimeSegments (by decide : 103284781 ≤ 103350317)
    (by decide : 103350317 ≤ 103415853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 103284781 103415853).card = 528 := join_1_0

end S049C04
end Sude.GeneratedTwinScan
