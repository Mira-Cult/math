import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S044C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 93061165 93093933 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 93061165 93093933).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 93061165 93093933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 93093933 93126701 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 93093933 93126701).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 93093933 93126701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 93126701 93159469 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 93126701 93159469).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 93126701 93159469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 93159469 93192237 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 93159469 93192237).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 93159469 93192237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 93061165 93126701).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 93061165 ≤ 93093933)
    (by decide : 93093933 ≤ 93126701) block0 block1

theorem join_0_1 : (twinPrimeSegment 93126701 93192237).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 93126701 ≤ 93159469)
    (by decide : 93159469 ≤ 93192237) block2 block3

theorem join_1_0 : (twinPrimeSegment 93061165 93192237).card = 509 := by
  simpa using combineTwinPrimeSegments (by decide : 93061165 ≤ 93126701)
    (by decide : 93126701 ≤ 93192237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 93061165 93192237).card = 509 := join_1_0

end S044C06
end Sude.GeneratedTwinScan
