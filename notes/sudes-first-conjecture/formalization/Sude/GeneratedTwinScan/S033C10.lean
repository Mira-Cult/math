import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S033C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70516781 70549549 = 144 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 70516781 70549549).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70516781 70549549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70549549 70582317 = 145 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 70549549 70582317).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70549549 70582317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70582317 70615085 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 70582317 70615085).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70582317 70615085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70615085 70647853 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 70615085 70647853).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70615085 70647853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 70516781 70582317).card = 289 := by
  simpa using combineTwinPrimeSegments (by decide : 70516781 ≤ 70549549)
    (by decide : 70549549 ≤ 70582317) block0 block1

theorem join_0_1 : (twinPrimeSegment 70582317 70647853).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 70582317 ≤ 70615085)
    (by decide : 70615085 ≤ 70647853) block2 block3

theorem join_1_0 : (twinPrimeSegment 70516781 70647853).card = 548 := by
  simpa using combineTwinPrimeSegments (by decide : 70516781 ≤ 70582317)
    (by decide : 70582317 ≤ 70647853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 70516781 70647853).card = 548 := join_1_0

end S033C10
end Sude.GeneratedTwinScan
