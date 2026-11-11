import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S045C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95027245 95060013 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 95027245 95060013).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95027245 95060013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95060013 95092781 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 95060013 95092781).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95060013 95092781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95092781 95125549 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 95092781 95125549).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95092781 95125549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95125549 95158317 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 95125549 95158317).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95125549 95158317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 95027245 95092781).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 95027245 ≤ 95060013)
    (by decide : 95060013 ≤ 95092781) block0 block1

theorem join_0_1 : (twinPrimeSegment 95092781 95158317).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 95092781 ≤ 95125549)
    (by decide : 95125549 ≤ 95158317) block2 block3

theorem join_1_0 : (twinPrimeSegment 95027245 95158317).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 95027245 ≤ 95092781)
    (by decide : 95092781 ≤ 95158317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 95027245 95158317).card = 471 := join_1_0

end S045C05
end Sude.GeneratedTwinScan
