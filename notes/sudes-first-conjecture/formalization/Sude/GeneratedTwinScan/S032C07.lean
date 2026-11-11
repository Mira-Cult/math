import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S032C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68026413 68059181 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 68026413 68059181).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68026413 68059181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68059181 68091949 = 147 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 68059181 68091949).card = 147 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68059181 68091949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68091949 68124717 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 68091949 68124717).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68091949 68124717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 68124717 68157485 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 68124717 68157485).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 68124717 68157485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 68026413 68091949).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 68026413 ≤ 68059181)
    (by decide : 68059181 ≤ 68091949) block0 block1

theorem join_0_1 : (twinPrimeSegment 68091949 68157485).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 68091949 ≤ 68124717)
    (by decide : 68124717 ≤ 68157485) block2 block3

theorem join_1_0 : (twinPrimeSegment 68026413 68157485).card = 540 := by
  simpa using combineTwinPrimeSegments (by decide : 68026413 ≤ 68091949)
    (by decide : 68091949 ≤ 68157485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 68026413 68157485).card = 540 := join_1_0

end S032C07
end Sude.GeneratedTwinScan
