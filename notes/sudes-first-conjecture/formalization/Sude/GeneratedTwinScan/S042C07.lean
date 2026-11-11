import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S042C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 88997933 89030701 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 88997933 89030701).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 88997933 89030701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89030701 89063469 = 149 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 89030701 89063469).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89030701 89063469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89063469 89096237 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 89063469 89096237).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89063469 89096237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89096237 89129005 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 89096237 89129005).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89096237 89129005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 88997933 89063469).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 88997933 ≤ 89030701)
    (by decide : 89030701 ≤ 89063469) block0 block1

theorem join_0_1 : (twinPrimeSegment 89063469 89129005).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 89063469 ≤ 89096237)
    (by decide : 89096237 ≤ 89129005) block2 block3

theorem join_1_0 : (twinPrimeSegment 88997933 89129005).card = 533 := by
  simpa using combineTwinPrimeSegments (by decide : 88997933 ≤ 89063469)
    (by decide : 89063469 ≤ 89129005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 88997933 89129005).card = 533 := join_1_0

end S042C07
end Sude.GeneratedTwinScan
