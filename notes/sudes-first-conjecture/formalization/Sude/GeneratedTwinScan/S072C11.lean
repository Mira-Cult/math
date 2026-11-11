import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S072C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152436781 152469549 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 152436781 152469549).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152436781 152469549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152469549 152502317 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 152469549 152502317).card = 105 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152469549 152502317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152502317 152535085 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 152502317 152535085).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152502317 152535085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152535085 152567853 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 152535085 152567853).card = 101 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152535085 152567853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 152436781 152502317).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 152436781 ≤ 152469549)
    (by decide : 152469549 ≤ 152502317) block0 block1

theorem join_0_1 : (twinPrimeSegment 152502317 152567853).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 152502317 ≤ 152535085)
    (by decide : 152535085 ≤ 152567853) block2 block3

theorem join_1_0 : (twinPrimeSegment 152436781 152567853).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 152436781 ≤ 152502317)
    (by decide : 152502317 ≤ 152567853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 152436781 152567853).card = 467 := join_1_0

end S072C11
end Sude.GeneratedTwinScan
